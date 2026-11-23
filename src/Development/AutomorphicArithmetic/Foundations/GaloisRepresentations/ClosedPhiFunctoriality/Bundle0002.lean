module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0693
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.FixWHolds
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.fixW_holds :
    FixW := by
  intro l _ K bk P AI T n hn s
  set x := f0 bk s with hx
  have hact := ActLaws.act_laws l
  have hσB : ∀ (g : GQ l) (y : Per.Acris l), Per.σB g (iB l y) = iB l (sigA g y) :=
    hact.2.2.2.2.2.2.2.2.2.2.2.1
  have hφB : ∀ y : Per.Acris l, Per.φB l (iB l y) = iB l (phiA l y) :=
    hact.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, hσι⟩ := _root_.GlobalTheory.AcrisFrobE.main l K bk
  have hfix : ∀ g : ↥(GK K), sigA (g : GQ l) x = x := by
    intro g
    have hxe : x = iA l (WittVector.frobenius (bk.ev (PowerSeries.C (PowerSeries.constantCoeff s)))) := by
      simp only [hx, f0, fA, RingHom.comp_apply, bk.ev_frob]
    rw [hxe, hσι, ← GlobalTheory.RingBasics.φA_apply, ← ActLaws.φA_σA, bk.ev_C, bk.gal_w g]
  have hinj : Function.Injective (iB l) := GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l
  set b := T.eB.symm (iB l x) with hb
  have hbfix : ∀ g : ↥(GK K), (P.PD K).actB g b = b := by
    intro g
    apply T.eB.injective
    rw [P.PD_actB, T.actB, hb, RingEquiv.apply_symm_apply, hσB, hfix]
  obtain ⟨c, hc⟩ := (P.PD K).invB b hbfix
  have hc' : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨c, c.2.2⟩ = b := hc
  have hit : ∀ (m : ℕ) (y : ↥(MaximalUnramifiedExtension l)), (fun z => P.φB z)^[m] (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B y) =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ((frobUr l ^ m) y) := by
    intro m y
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, phiB_algebraMap, pow_succ', AlgHom.mul_apply]
  have hbn : (fun z => P.φB z)^[n] b = b := by
    rw [← hc', hit, hn ⟨c, c.2.2⟩ c.2.1]
  have htr : ∀ (m : ℕ) (y : P.R.B), T.eB ((fun z => P.φB z)^[m] y) = (Per.φB l)^[m] (T.eB y) := by
    intro m y
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', T.frob, ih]
  have hin : ∀ (m : ℕ) (y : Per.Acris l), (Per.φB l)^[m] (iB l y) = iB l ((phiA l)^[m] y) := by
    intro m y
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hφB]
  apply hinj
  have h1 := htr n b
  rw [hbn, hb, RingEquiv.apply_symm_apply, hin] at h1
  rw [RingHom.coe_pow]
  exact h1.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.FrExHolds
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.frEx_holds :
    FrEx := by
  intro l _ K L₀ bk τp hτp P AI T a hL₀ r Cl Cv J hCl hcr
  haveI := K.2
  let N : ℕ := Finset.univ.sup fun τ' : ↥K.1 →ₐ[ℚ_[l]] Om l => ((J τ').map Int.natAbs).sup
  have hN : ∀ τ', ∀ n ∈ J τ', |n| ≤ (N : ℤ) := by
    intro τ' n hn
    rw [Int.abs_eq_natAbs]
    have h1 : n.natAbs ≤ ((J τ').map Int.natAbs).sup := Multiset.le_sup (Multiset.mem_map_of_mem _ hn)
    have h2 : ((J τ').map Int.natAbs).sup ≤ N :=
      Finset.le_sup (f := fun τ' : ↥K.1 →ₐ[ℚ_[l]] Om l => ((J τ').map Int.natAbs).sup) (Finset.mem_univ τ')
    exact_mod_cast h1.trans h2
  have hsstCl : ∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1)
      (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) →
      (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R :=
    fun ρ₁ h L r' R h1 h2 h3 => (hCl ρ₁ h L r' R h1 h2 h3).1
  have hsst : ∀ m, IsSst P (qRep (Cv.tw.ρ' m)) := fun m =>
    (_root_.GlobalTheory.LayerSst.main l K L₀ P AI T a Cl _ (Cv.tw.ρ' m) (Cv.lay m)).1 hsstCl
  have hfr : ∀ m, ∃ F : Frame bk N (Cv.tw.d' m) (fun g => (Cv.tw.ρ' m g).val),
      F.IsDR ∧ (IsCrys (P.PD K) (qRep (Cv.tw.ρ' m)) → F.IsCr) := fun m =>
    GlobalTheory.T.exists_breuilKisinFrame_semistable_boundedJumps l K bk τp hτp P AI T N _ (Cv.tw.ρ' m) (Cv.cont' m) (hsst m)
      (GlobalTheory.T.layer_DdR_bounds_alt l K L₀ P AI T a Cl J N hL₀ hN _ (Cv.tw.ρ' m) (Cv.lay m) hCl)
  choose F hFdr hFcr using hfr
  obtain ⟨F₀, -, hF₀cr, rr, hlink⟩ := GlobalTheory.T.exists_deRhamFrame_limitLattice_breuilKisinTower l K bk τp hτp Cv.d N Cv.ρ Cv.tw F hFdr
  have hFc : ∀ m, (F m).IsCr := fun m =>
    hFcr m ((_root_.GlobalTheory.LayerSst.main l K L₀ P AI T a Cl _ (Cv.tw.ρ' m) (Cv.lay m)).2 hcr)
  exact ⟨N, F, F₀, rr, hFc, hF₀cr hFc, hlink⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.FuncHolds
section
noncomputable section

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

open Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Per

theorem func_holds : IntBasis → Func := by
  intro hB l _ F I _ x z hx hz
  classical
  letI : Fintype I := Fintype.ofFinite I
  let eqv := Fintype.equivFin (Option I)
  let y : Fin (Fintype.card (Option I)) → Om l := fun k => (eqv.symm k).elim z x
  have hy : ∀ k, ‖y k‖ ≤ 1 := by
    intro k
    dsimp only [y]
    cases eqv.symm k with
    | none => simpa using hz
    | some i => simpa using hx i
  obtain ⟨m, e, hli, he, hc⟩ := hB l F _ y hy
  choose c hc1 hc2 using hc
  have hyz : y (eqv none) = z := by simp [y]
  have hyx : ∀ i, y (eqv (some i)) = x i := by intro i; simp [y]
  by_cases hz0 : z = 0
  · refine ⟨0, ?_, ?_, ?_⟩ <;> simp [hz0]
  have hm : (Finset.univ : Finset (Fin m)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply hz0
    rw [← hyz, hc2, hne, Finset.sum_empty]
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ
    (fun j => ‖((c (eqv none) j : ↥F) : Om l)‖) hm
  let f : (Fin m → ↥F) →ₗ[↥F] Om l := Fintype.linearCombination ↥F e
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro a ha
    funext j
    exact Fintype.linearIndependent_iff.1 hli a (by simpa [f, Fintype.linearCombination_apply] using ha) j
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective f hker
  let lam : Om l →ₗ[↥F] ↥F := LinearMap.proj j₀ ∘ₗ G
  have key : ∀ a : Fin m → ↥F, lam (∑ j, (a j : Om l) * e j) = a j₀ := by
    intro a
    have h1 : (∑ j, (a j : Om l) * e j) = f a := by
      simp only [f, Fintype.linearCombination_apply]
      rfl
    have h2 : G (f a) = a := by
      have := LinearMap.congr_fun hG a
      simpa using this
    rw [h1]
    simp only [lam, LinearMap.comp_apply, h2, LinearMap.proj_apply]
  have hlz : lam z = c (eqv none) j₀ := by
    rw [← hyz, hc2, key]
  refine ⟨lam, ?_, ?_, ?_⟩
  · intro i
    rw [← hyx i, hc2, key]
    exact hc1 _ _
  · rw [hlz]
    rw [← hyz, hc2]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_
    intro j _
    rw [norm_mul]
    calc ‖((c (eqv none) j : ↥F) : Om l)‖ * ‖e j‖
        ≤ ‖((c (eqv none) j : ↥F) : Om l)‖ * 1 :=
          mul_le_mul_of_nonneg_left (he j) (norm_nonneg _)
      _ = ‖((c (eqv none) j : ↥F) : Om l)‖ := mul_one _
      _ ≤ _ := hj₀ j (Finset.mem_univ j)
  · rw [hlz]
    exact hc1 _ _

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasis
section
noncomputable section

open Formalism.BasicNotions.Loc

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem linearIndependent_update_sum_of_ne_zero {l : ℕ} [Fact (Nat.Prime l)] {F : IntermediateField ℚ_[l] (Om l)} {m : ℕ}
    (e : Fin m → Om l) (hLI : LinearIndependent F e) (a : Fin m → F) (j0 : Fin m) (ha : a j0 ≠ 0) :
    LinearIndependent F (Function.update e j0 (∑ j, (a j : Om l) * e j)) := by
  rw [Fintype.linearIndependent_iff] at hLI ⊢
  intro g hg
  have key : ∑ j, (g j + g j0 * a j - if j = j0 then g j0 else 0) • e j = 0 := by
    rw [← hg]
    have h1 : ∀ j, (g j + g j0 * a j - if j = j0 then g j0 else 0) • e j
        = g j • e j + (g j0 : Om l) * ((a j : Om l) * e j) - (if j = j0 then (g j0 : Om l) * e j0 else 0) := by
      intro j
      by_cases h : j = j0
      · subst h
        rw [if_pos rfl, if_pos rfl]
        show ((g j + g j * a j - g j : F) : Om l) * e j = (g j : Om l) * e j + _ - _
        push_cast
        ring
      · rw [if_neg h, if_neg h]
        show ((g j + g j0 * a j - 0 : F) : Om l) * e j = (g j : Om l) * e j + _ - _
        push_cast
        ring
    have h2 : ∀ j, g j • Function.update e j0 (∑ i, (a i : Om l) * e i) j
        = g j • e j + (if j = j0 then (g j0 : Om l) * (∑ i, (a i : Om l) * e i) - (g j0 : Om l) * e j0 else 0) := by
      intro j
      by_cases h : j = j0
      · subst h
        rw [Function.update_self, if_pos rfl]
        show (g j : Om l) * _ = (g j : Om l) * e j + _
        ring
      · rw [Function.update_of_ne h, if_neg h, add_zero]
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_congr rfl (fun j _ => h2 j)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, ← Finset.mul_sum]
    ring
  have hz := hLI _ key
  have h0 : g j0 = 0 := by
    have h3 := hz j0
    rw [if_pos rfl] at h3
    have h4 : g j0 * a j0 = 0 := by linear_combination h3
    rcases mul_eq_zero.1 h4 with h | h
    · exact h
    · exact absurd h ha
  intro j
  have h5 := hz j
  rw [h0] at h5
  simpa using h5

private theorem exists_bounded_coeffs_after_update {l : ℕ} [Fact (Nat.Prime l)] {F : IntermediateField ℚ_[l] (Om l)} {m : ℕ}
    (e : Fin m → Om l) (a c : Fin m → F) (j0 : Fin m) (ha : 1 < ‖(a j0 : Om l)‖)
    (hmax : ∀ j, ‖(a j : Om l)‖ ≤ ‖(a j0 : Om l)‖) (hc : ∀ j, ‖(c j : Om l)‖ ≤ 1) :
    ∃ c' : Fin m → F, (∀ j, ‖(c' j : Om l)‖ ≤ 1) ∧
      ∑ j, (c j : Om l) * e j = ∑ j, (c' j : Om l) * Function.update e j0 (∑ i, (a i : Om l) * e i) j := by
  have ha0 : (a j0 : Om l) ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    linarith
  have hpos : 0 < ‖(a j0 : Om l)‖ := by linarith
  refine ⟨fun j => if j = j0 then c j0 / a j0 else c j - c j0 * a j / a j0, ?_, ?_⟩
  · intro j
    by_cases h : j = j0
    · simp only [if_pos h]
      push_cast
      rw [norm_div, div_le_one hpos]
      linarith [hc j0]
    · simp only [if_neg h]
      push_cast
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc j) ?_)
      rw [norm_neg, norm_div, norm_mul, div_le_one hpos]
      calc ‖(c j0 : Om l)‖ * ‖(a j : Om l)‖ ≤ 1 * ‖(a j0 : Om l)‖ :=
            mul_le_mul (hc j0) (hmax j) (norm_nonneg _) zero_le_one
        _ = ‖(a j0 : Om l)‖ := one_mul _
  · set y := ∑ i, (a i : Om l) * e i with hy
    have h1 : ∀ j, ((if j = j0 then c j0 / a j0 else c j - c j0 * a j / a j0 : F) : Om l) * Function.update e j0 y j
        = (c j : Om l) * e j - ((c j0 : Om l) / (a j0 : Om l)) * ((a j : Om l) * e j)
          + (if j = j0 then ((c j0 : Om l) / (a j0 : Om l)) * y else 0) := by
      intro j
      by_cases h : j = j0
      · subst h
        rw [if_pos rfl, if_pos rfl, Function.update_self]
        push_cast
        field_simp
        ring
      · rw [if_neg h, if_neg h, Function.update_of_ne h]
        push_cast
        ring
    rw [Finset.sum_congr rfl (fun j _ => h1 j)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, ← Finset.mul_sum, ← hy]
    ring

private theorem exists_bounded_independent_spanning_family {l : ℕ} [Fact (Nat.Prime l)] (F : IntermediateField ℚ_[l] (Om l)) (n : ℕ) :
    ∀ x : Fin n → Om l, (∀ i, ‖x i‖ ≤ 1) → ∃ (m : ℕ) (e : Fin m → Om l), LinearIndependent F e ∧
      (∀ j, ‖e j‖ ≤ 1) ∧ ∀ i, ∃ c : Fin m → F, (∀ j, ‖(c j : Om l)‖ ≤ 1) ∧ x i = ∑ j, (c j : Om l) * e j := by
  induction n with
  | zero =>
    intro x _
    exact ⟨0, Fin.elim0, linearIndependent_empty_type, fun j => j.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro x hx
    obtain ⟨m, e, hLI, he, hc⟩ := ih (fun i => x (Fin.castSucc i)) (fun i => hx _)
    by_cases hy : x (Fin.last n) ∈ Submodule.span F (Set.range e)
    · obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hy
      have ha' : x (Fin.last n) = ∑ j, (a j : Om l) * e j := ha.symm
      by_cases hb : ∀ j, ‖(a j : Om l)‖ ≤ 1
      · refine ⟨m, e, hLI, he, fun i => ?_⟩
        induction i using Fin.lastCases with
        | last => exact ⟨a, hb, ha'⟩
        | cast i => exact hc i
      · push_neg at hb
        obtain ⟨j1, hj1⟩ := hb
        haveI : Nonempty (Fin m) := ⟨j1⟩
        obtain ⟨j0, hj0⟩ := Finite.exists_max (fun j => ‖(a j : Om l)‖)
        have ha1 : 1 < ‖(a j0 : Om l)‖ := lt_of_lt_of_le hj1 (hj0 j1)
        have ha0 : a j0 ≠ 0 := by
          intro h
          rw [h] at ha1
          norm_num at ha1
        refine ⟨m, Function.update e j0 (x (Fin.last n)), ?_, ?_, ?_⟩
        · rw [ha']
          exact linearIndependent_update_sum_of_ne_zero e hLI a j0 ha0
        · intro j
          by_cases h : j = j0
          · subst h
            rw [Function.update_self]
            exact hx _
          · rw [Function.update_of_ne h]
            exact he j
        · intro i
          induction i using Fin.lastCases with
          | last =>
            refine ⟨Pi.single j0 1, ?_, ?_⟩
            · intro j
              by_cases h : j = j0
              · subst h
                simp
              · simp [Pi.single_apply, h]
            · rw [Finset.sum_eq_single j0]
              · simp
              · intro j _ h
                simp [Pi.single_apply, h]
              · simp
          | cast i =>
            obtain ⟨c, hc1, hc2⟩ := hc i
            obtain ⟨c', hc'1, hc'2⟩ := exists_bounded_coeffs_after_update e a c j0 ha1 hj0 hc1
            refine ⟨c', hc'1, ?_⟩
            rw [hc2, hc'2, ← ha']
    · refine ⟨m + 1, (Fin.snoc e (x (Fin.last n)) : Fin (m + 1) → Om l),
        linearIndependent_finSnoc.2 ⟨hLI, hy⟩, ?_, ?_⟩
      · intro j
        induction j using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last]
          exact hx _
        | cast j =>
          rw [Fin.snoc_castSucc]
          exact he j
      · intro i
        induction i using Fin.lastCases with
        | last =>
          refine ⟨(Fin.snoc (0 : Fin m → F) 1 : Fin (m + 1) → F), ?_, ?_⟩
          · intro j
            induction j using Fin.lastCases with
            | last => simp
            | cast j => simp
          · simp [Fin.sum_univ_castSucc]
        | cast i =>
          obtain ⟨c, hc1, hc2⟩ := hc i
          refine ⟨(Fin.snoc c 0 : Fin (m + 1) → F), ?_, ?_⟩
          · intro j
            induction j using Fin.lastCases with
            | last => simp
            | cast j => simp [hc1 j]
          · simp [Fin.sum_univ_castSucc, hc2]

theorem intBasis_holds : IntBasis := fun l _ F n x hx => exists_bounded_independent_spanning_family F n x hx

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.InvUHolds
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem invU_holds : InvU := by
  intro l _ K bk τ hτ
  have hFφ : ∀ a : Ainf l, WittVector.frobenius a = Per.φA l a := fun a => (GlobalTheory.RingBasics.φA_apply l a).symm
  set f : Ainf l →+* Per.Bcris l := (Per.aB l).comp (Per.φA l) with hf
  set alg : Per.Acris l →+* Per.Bcris l := algebraMap (Per.Acris l) (Per.Bcris l) with halg
  have hif : ∀ a : Ainf l, iB l (fI l a) = f a := fun a => by
    simp only [fI, iB, iA, hFφ, hf, RingHom.comp_apply, GlobalTheory.RingIface.aB_eq_alg]
  have hw : IsUnit (f τ) := by
    obtain ⟨-, e, η, ⟨he1, he2⟩, hτe⟩ := hτ
    have hne : e ≠ 1 := by
      rintro rfl; apply he2; simp
    have hmu : IsUnit (Per.aB l (WittVector.teichmuller l e - 1)) :=
      GlobalTheory.CrisLoc.unit_of_root_aB l e he1 hne
    have : f τ = Per.aB l (η : Ainf l) * Per.aB l (WittVector.teichmuller l e - 1) := by
      simp only [hf, RingHom.comp_apply, ← hFφ, hτe, map_mul]
    rw [this]; exact (η.isUnit.map _).mul hmu
  refine ⟨by rw [hif]; exact hw, ?_⟩
  intro N k d ρ F Y Y' Q Q' hY hYY hQQ hε
  have hgal : ∀ g : ↥(GK K), τ ^ N • ((ρ g).val.map (Per.zA l) * Y.map (Per.σA (g : GQ l))) =
      Per.σA (g : GQ l) τ ^ N • (Y * F.ε g) :=
    (GlobalTheory.T.frame_ainf_matrix_frobenius_galois_eqs l K bk τ hτ N d _ F Y Y' hY hYY).2.1
  have e2 : (⇑alg ∘ ⇑(fI l)) = ⇑f := funext hif
  obtain ⟨W, hW⟩ := hw.pow N
  set A := Y.map f with hA
  set B := Q.map alg with hB
  refine ⟨((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B), ⟨?_, ?_⟩, ?_⟩
  ·
    have hB' : B * Q'.map alg = alg ((l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l)) := by
      rw [hB, ← Matrix.map_mul, hQQ, GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _)]
    have hA' : A * Y'.map f = f τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l)) := by
      rw [hA, ← Matrix.map_mul, hYY, GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _), map_pow]
    have hc : IsUnit (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * alg ((l : Per.Acris l) ^ (2 * k)) * f τ ^ (2 * N)) := by
      refine (W⁻¹.isUnit.mul ?_).mul (hw.pow _)
      have h := (isUnit_l_Bcris l).pow (2 * k)
      simpa [halg, map_pow, map_natCast] using h
    obtain ⟨c, hcv⟩ := hc
    set V := Q'.map alg * Y'.map f
    have hUV : (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B)) * V = (c : Per.Bcris l) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l)) := by
      rw [hcv, smul_mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc B, hB', smul_mul_assoc, Matrix.one_mul,
        mul_smul_comm, hA', smul_smul, smul_smul, mul_assoc]
    have h1 : (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B)) * (((c⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • V) = 1 := by
      rw [Matrix.mul_smul, hUV, smul_smul, Units.inv_mul, one_smul]
    exact ⟨⟨_, _, h1, mul_eq_one_comm.mp h1⟩, rfl⟩
  · intro g
    set σ := Per.σB (g : GQ l) with hσ
    have hσaB : ∀ a : Ainf l, σ (Per.aB l a) = Per.aB l (Per.σA (g : GQ l) a) :=
      (ActLaws.act_laws l).2.2.2.2.2.1 (g : GQ l)
    have hσf : ∀ a : Ainf l, σ (f a) = f (Per.σA (g : GQ l) a) := fun a => by
      simp only [hf, RingHom.comp_apply, hσaB, ActLaws.φA_σA]
    have hfz : ∀ z : ℤ_[l], f (Per.zA l z) = Per.zB l z := fun z => by
      simp only [hf, RingHom.comp_apply, GlobalTheory.RingIface.zB_eq_aB_zA, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1 z]
    have hσalg : ∀ x : Per.Acris l, σ (alg x) = alg (sigA (g : GQ l) x) :=
      (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1 (g : GQ l)
    have hG := congrArg (fun M => M.map f) (hgal g)
    simp only [GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_mul, Matrix.map_map, map_pow] at hG
    have e1 : (⇑f ∘ ⇑(Per.zA l)) = ⇑(Per.zB l) := funext hfz
    rw [e1, ← hσf] at hG
    have hE := congrArg (fun M => M.map alg) (hε g)
    simp only [Matrix.map_mul, Matrix.map_map] at hE
    rw [e2] at hE
    have eA : A.map σ = Y.map (⇑f ∘ ⇑(Per.σA (g : GQ l))) := by
      rw [hA, Matrix.map_map]; congr 1; funext a; exact hσf a
    have eB : B.map σ = Q.map (⇑alg ∘ ⇑(sigA (g : GQ l))) := by
      rw [hB, Matrix.map_map]; congr 1; funext a; exact hσalg a
    rw [GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_mul, eA, eB]
    have hsW : σ ((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * σ (W : Per.Bcris l) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hσW : σ (f τ) ^ N = σ (W : Per.Bcris l) := by rw [hW, map_pow]
    rw [hσW, ← hW] at hG
    have hZ : (ρ g).val.map (Per.zB l) * Y.map (⇑f ∘ ⇑(Per.σA (g : GQ l))) =
        (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * σ (W : Per.Bcris l)) • (A * (F.ε g).map f) := by
      rw [← smul_smul, ← hG, smul_smul, Units.inv_mul, one_smul]
    rw [mul_smul_comm, ← Matrix.mul_assoc, hZ, smul_mul_assoc, Matrix.mul_assoc, hE, smul_smul, mul_left_comm, hsW,
      mul_one]
  · rw [hif, ← hW, smul_smul, Units.mul_inv, one_smul, hA, hB, Matrix.map_mul, Matrix.map_map]
    have e3 : (⇑(iB l) ∘ ⇑(fI l)) = ⇑f := funext hif
    rw [e3]

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

