module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TridiagonalWeilDeligne
section
noncomputable section

open Module

namespace UpperTheory

private theorem tri_mul_diag {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hA i k h, zero_mul]
  · rw [hB k i h, mul_zero]

private theorem tri_avg {G : Type} [Group G] [Finite G] {n : ℕ} (R : G →* Matrix (Fin n) (Fin n) ℂ)
    (hR : ∀ g i j, j < i → R g i j = 0) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P.det ∧ ∀ g, R g * P = P * Matrix.diagonal (fun i => R g i i) := by
  classical
  letI := Fintype.ofFinite G
  have hm : ∀ g h i, R (g * h) i i = R g i i * R h i i := fun g h i => by
    rw [map_mul]; exact tri_mul_diag _ _ (hR g) (hR h) i
  refine ⟨∑ h, R h * Matrix.diagonal (fun i => R h⁻¹ i i), ?_, fun g => ?_⟩
  · rw [Matrix.det_of_upperTriangular]
    · rw [isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
      intro i _
      have : (∑ h, R h * Matrix.diagonal (fun i => R h⁻¹ i i)) i i = (Fintype.card G : ℂ) := by
        rw [Matrix.sum_apply]
        have : ∀ h : G, (R h * Matrix.diagonal (fun i => R h⁻¹ i i)) i i = 1 := fun h => by
          rw [Matrix.mul_diagonal, ← hm, mul_inv_cancel, map_one, Matrix.one_apply_eq]
        simp [this]
      rw [this]
      exact_mod_cast Fintype.card_ne_zero
    · intro i j hij
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero fun h _ => ?_
      rw [Matrix.mul_diagonal, hR h i j hij, zero_mul]
  · rw [Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
    rw [Equiv.coe_mulLeft, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, map_mul, Matrix.mul_assoc]
    congr 3
    funext i
    rw [← hm]
    congr 2
    group

theorem tridiagonal_weil_deligne : UpperTheory.V.Af.Wd.TriDiag := by
  intro W I _ _ _ n ρ d hfin ⟨b, hb⟩
  let G := ρ.toHomUnits.range
  haveI : Finite G := by
    haveI : Finite (Set.range ρ) := hfin
    refine Finite.of_injective (fun g : G => (⟨(g.1 : End ℂ W), ?_⟩ : Set.range ρ)) ?_
    · obtain ⟨s, hs⟩ := g.2
      exact ⟨s, by rw [← hs]; rfl⟩
    · intro x y h
      exact Subtype.ext (Units.ext (congrArg Subtype.val h))
  let R : G →* Matrix (Fin n) (Fin n) ℂ :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp (Units.coeHom _)).comp G.subtype
  have hRs : ∀ s, R (ρ.toHomUnits.rangeRestrict s) = LinearMap.toMatrix b b (ρ s) := fun s => rfl
  obtain ⟨P, hP, hRP⟩ := tri_avg R (fun g i j hij => by
    obtain ⟨s, rfl⟩ := ρ.toHomUnits.rangeRestrict_surjective g
    rw [hRs]; exact (hb s).1 i j hij)
  let e := Matrix.toLinearEquiv b P hP
  have he : ∀ x, e x = Matrix.toLin b b P x := fun x => rfl
  refine ⟨b.map e, fun s => ?_⟩
  have h1 := hRP (ρ.toHomUnits.rangeRestrict s)
  rw [hRs] at h1
  have h2 : (fun i => LinearMap.toMatrix b b (ρ s) i i) = d s := funext (hb s).2
  rw [h2] at h1
  have h3 : ∀ j, ρ s (b.map e j) = d s j • b.map e j := fun j => by
    have h4 := congrArg (fun M => Matrix.toLin b b M (b j)) h1
    simp only [Matrix.toLin_mul b b b, Matrix.toLin_toMatrix, LinearMap.comp_apply] at h4
    rw [Basis.map_apply, he, h4, ← map_smul]
    congr 1
    rw [Matrix.toLin_self]
    simp [Matrix.diagonal_apply, ite_smul, Finset.sum_ite_eq']
  ext i j
  rw [LinearMap.toMatrix_apply, h3, map_smul, Basis.repr_self, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Finsupp.single_apply, Ne.symm h]

end UpperTheory
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneFunctorExact
section
open TensorProduct Module GlobalTheory.Pst GlobalTheory.Pst.DpstMap in
theorem UpperTheory.weilDeligne_functor_exact :
    UpperTheory.V.Af.Wd.LetterExact := by
  intro LL U D' D D'' F _ _ _ _ _ _ _ _ _ _ m' m m'' τ T S hT hS hex hsurj
  have hS' : Function.Surjective (S.baseChange F) := LinearMap.lTensor_surjective F hsurj
  have hex' : Function.Exact (T.baseChange F) (S.baseChange F) := lTensor_exact F hex hsurj
  have eT : ∀ y, letterLin m' m F τ T hT (letterQ m' F τ y) = letterQ m F τ (T.baseChange F y) := fun _ => rfl
  have eS : ∀ y, letterLin m m'' F τ S hS (letterQ m F τ y) = letterQ m'' F τ (S.baseChange F y) := fun _ => rfl
  have hker : letterKer m'' F τ ≤ (letterKer m F τ).map (S.baseChange F) := iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    obtain ⟨y, rfl⟩ := hS' y
    refine ⟨_, Submodule.mem_iSup_of_mem c ⟨y, rfl⟩, ?_⟩
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange F) (hS c)) y
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply] at this
    simp [this]
  refine ⟨fun y => ?_, fun y => ?_⟩
  · obtain ⟨y, rfl⟩ := letterQ_surjective m F τ y
    constructor
    · intro h
      rw [eS, ← LinearMap.mem_ker, ker_letterQ] at h
      obtain ⟨z, hz, hzy⟩ := hker h
      obtain ⟨w, hw⟩ := (hex' (y - z)).mp (by rw [map_sub, hzy, sub_self])
      refine ⟨letterQ m' F τ w, ?_⟩
      have hz0 : letterQ m F τ z = 0 := by
        rw [← LinearMap.mem_ker, ker_letterQ]; exact hz
      rw [eT, hw, map_sub, hz0, sub_zero]
    · rintro ⟨w, hw⟩
      obtain ⟨w, rfl⟩ := letterQ_surjective m' F τ w
      rw [← hw, eT, eS, hex'.apply_apply_eq_zero, map_zero]
  · obtain ⟨y, rfl⟩ := letterQ_surjective m'' F τ y
    obtain ⟨y, rfl⟩ := hS' y
    exact ⟨letterQ m F τ y, eS y⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneMonodromyUpperTriangular
section
theorem UpperTheory.weilDeligne_monodromy_upperTriangular :
    UpperTheory.V.Af.Wd.TriMono := by
  intro k W Γ _ _ _ n N ρ c μ hcomm hT hN
  obtain ⟨b, hb⟩ := hT
  set B := LinearMap.toMatrix b b N with hBdef
  have hAlow : ∀ σ (i j : Fin n), j < i → LinearMap.toMatrix b b (ρ σ) i j = 0 := fun σ => (hb (some σ)).1
  have hAdiag : ∀ σ (i : Fin n), LinearMap.toMatrix b b (ρ σ) i i = μ σ i := fun σ => (hb (some σ)).2
  have hB0 : B ≠ 0 := by
    intro h
    apply hN
    apply (LinearMap.toMatrix b b).injective
    rw [← hBdef, h, map_zero]
  have hex : ∃ i j, B i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hB0 (Matrix.ext h)
  classical
  have hJ : (Finset.univ.filter fun j => ∃ i, B i j ≠ 0).Nonempty := by
    obtain ⟨i, j, h⟩ := hex
    exact ⟨j, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨i, h⟩⟩
  set j := (Finset.univ.filter fun j => ∃ i, B i j ≠ 0).min' hJ with hjdef
  have hjmem := Finset.min'_mem _ hJ
  rw [← hjdef] at hjmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjmem
  have hjmin : ∀ i l, l < j → B i l = 0 := by
    intro i l hl
    by_contra h
    have : j ≤ l := Finset.min'_le _ l (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨i, h⟩)
    exact absurd hl (not_lt.mpr this)
  have hI : (Finset.univ.filter fun i => B i j ≠ 0).Nonempty := by
    obtain ⟨i, h⟩ := hjmem
    exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h⟩
  set i := (Finset.univ.filter fun i => B i j ≠ 0).max' hI with hidef
  have himem := Finset.max'_mem _ hI
  rw [← hidef] at himem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at himem
  have himax : ∀ l, i < l → B l j = 0 := by
    intro l hl
    by_contra h
    have : l ≤ i := Finset.le_max' _ l (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
    exact absurd hl (not_lt.mpr this)
  refine ⟨i, j, fun σ => ?_⟩
  set A := LinearMap.toMatrix b b (ρ σ) with hAdef
  have hmat : A * B = c σ • (B * A) := by
    rw [hAdef, hBdef, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, ← map_smul, hcomm]
  have h1 : (A * B) i j = μ σ i * B i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hAdef, hAdiag]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hAdef, hAlow σ i l h, zero_mul]
      · rw [himax l h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : (B * A) i j = B i j * μ σ j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j, hAdef, hAdiag]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hjmin i l h, zero_mul]
      · rw [hAdef, hAlow σ l j h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have h3 := congrFun (congrFun hmat i) j
  rw [Matrix.smul_apply, h1, h2, smul_eq_mul] at h3
  have : (μ σ i - c σ * μ σ j) * B i j = 0 := by rw [sub_mul, h3]; ring
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h himem
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneRankOneLine
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp

private theorem zpow_apply_eig {F M : Type} [Field F] [AddCommGroup M] [Module F M] (u : (End F M)ˣ) (x : M) (c : F)
    (hc : c ≠ 0) (hx : (u : End F M) x = c • x) (n : ℤ) : ((u ^ n : (End F M)ˣ) : End F M) x = c ^ n • x := by
  have hi : ((u⁻¹ : (End F M)ˣ) : End F M) x = c⁻¹ • x := by
    rw [eq_inv_smul_iff₀ hc, ← map_smul, ← hx, ← End.mul_apply, Units.inv_mul, End.one_apply]
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, Units.val_mul, End.mul_apply, hx, map_smul, ih, smul_smul,
      zpow_add_one₀ hc, mul_comm]
  | pred n ih => rw [zpow_sub_one, Units.val_mul, End.mul_apply, hi, map_smul, ih, smul_smul,
      zpow_sub_one₀ hc, mul_comm]

private theorem key {F M : Type} [Field F] [AddCommGroup M] [Module F M] (u : (End F M)ˣ) (φ a : End F M)
    (hu : (u : End F M) = φ) (hcm : φ * a = a * φ) (x : M) (c s : F) (hc : c ≠ 0) (f : ℕ) (hφ : (φ ^ f) x = c • x)
    (hs : a x = s • x) (n : ℕ) (d : ℤ) :
    (a * ((u ^ (-((f : ℤ) * d)) : (End F M)ˣ) : End F M)) ((φ ^ n) x) = (c ^ (-d) * s) • (φ ^ n) x := by
  have hφ' : (φ ^ f) ((φ ^ n) x) = c • (φ ^ n) x := by
    rw [← End.mul_apply, ← pow_add, add_comm, pow_add, End.mul_apply, hφ, map_smul]
  have hs' : a ((φ ^ n) x) = s • (φ ^ n) x := by
    have hcm' : Commute φ a := hcm
    rw [← End.mul_apply, ← (hcm'.pow_left n).eq, End.mul_apply, hs, map_smul]
  have hz := zpow_apply_eig (u ^ f) _ c hc (by rw [Units.val_pow_eq_pow_val, hu]; exact hφ') (-d)
  rw [End.mul_apply, ← mul_neg, zpow_mul, zpow_natCast, hz, map_smul, hs', mul_smul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem UpperTheory.weil_deligne_rank_one_line :
    UpperTheory.V.Af.Wd.Line := by
  intro F Ω _ _ _ _ _ l _ P ι w A h O _ _ _ Bw hj L V _ _ _ _ _ ρ h1 hV x hx0 c hc hφ σ s hs y
  have hfin := hV.finite
  have hd : finrank ℂ (WDSpace P ι ρ) = 1 := by
    rw [LetterDim.finrank_wdSpace l P ι _ L _ _ hV, h1]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, wdMk P ι ρ ((phiD P ρ ^ n) x) ≠ 0 := by
    by_contra hh
    exact hx0 (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι _ L _ _ _ fun n => by_contra fun h0 => hh ⟨n, h0⟩)
  have hw : weilD Bw h P ρ σ ((phiD P ρ ^ n) x) = (c ^ (-deg σ) * s) • (phiD P ρ ^ n) x := by
    rw [weilD_apply]
    exact key (phiU P ρ) (phiD P ρ) _ (coe_phiU P ρ) (phiD_actD P ρ _) x c s hc _ hφ hs n _
  obtain ⟨d, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℂ) _ hn).mp hd y
  rw [map_smul, wdRho_mk, hw]
  change d • wdMk P ι ρ ((Dpst P ρ).module.toSMul.smul (c ^ (-deg σ) * s) ((phiD P ρ ^ n) x)) = _
  rw [wdMk_smul, smul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneTriangularInitialSegment
section
open Module

theorem UpperTheory.weilDeligne_triangular_initial_segment :
    UpperTheory.V.Af.Wd.TriInit := by
  intro k W ι _ _ _ n T d hT
  obtain ⟨b, hb⟩ := hT
  have hp : ∀ a x, b.coord (Fin.last n) (T a x) = d a (Fin.last n) * b.coord (Fin.last n) x := by
    intro a x
    have h : (b.coord (Fin.last n)) ∘ₗ (T a) = d a (Fin.last n) • b.coord (Fin.last n) := by
      refine b.ext fun j => ?_
      have h1 := (hb a).1 (Fin.last n) j
      have h2 := (hb a).2 (Fin.last n)
      rw [LinearMap.toMatrix_apply] at h1 h2
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, smul_eq_mul]
      by_cases hj : j = Fin.last n
      · subst hj
        rw [h2]; simp
      · rw [h1 (lt_of_le_of_ne (Fin.le_last j) hj), Finsupp.single_apply, if_neg hj, mul_zero]
    simpa using LinearMap.congr_fun h x
  have hS : ∀ a, ∀ x ∈ LinearMap.ker (b.coord (Fin.last n)), T a x ∈ LinearMap.ker (b.coord (Fin.last n)) := by
    intro a x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hp, hx, mul_zero]
  refine ⟨LinearMap.ker (b.coord (Fin.last n)), hS, b.coord (Fin.last n), ?_, rfl, hp, ?_⟩
  · intro c
    exact ⟨c • b (Fin.last n), by simp⟩
  · let v : Fin n → LinearMap.ker (b.coord (Fin.last n)) := fun i =>
      ⟨b (Fin.castSucc i), by
        rw [LinearMap.mem_ker, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply,
          if_neg (Fin.castSucc_lt_last i).ne]⟩
    have hv : LinearIndependent k v := by
      apply LinearIndependent.of_comp (LinearMap.ker (b.coord (Fin.last n))).subtype
      exact b.linearIndependent.comp Fin.castSucc (Fin.castSucc_injective n)
    have key : ∀ x : LinearMap.ker (b.coord (Fin.last n)),
        x = ∑ i, b.repr (x : W) (Fin.castSucc i) • v i := by
      intro x
      apply Subtype.ext
      have hx : b.repr (x : W) (Fin.last n) = 0 := x.2
      have h := b.sum_repr (x : W)
      rw [Fin.sum_univ_castSucc, hx, zero_smul, add_zero] at h
      rw [Submodule.coe_sum]
      exact h.symm
    have hsp : ⊤ ≤ Submodule.span k (Set.range v) := by
      intro x _
      rw [key x]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    let b' := Basis.mk hv hsp
    have hb' : ∀ i, b' i = v i := fun i => Basis.mk_apply hv hsp i
    have hr : ∀ (x : LinearMap.ker (b.coord (Fin.last n))) i, b'.repr x i = b.repr (x : W) (Fin.castSucc i) := by
      intro x i
      have h := congrFun (b'.repr_sum_self fun i => b.repr (x : W) (Fin.castSucc i)) i
      simp only [hb'] at h
      rw [← key x] at h
      exact h
    have hm : ∀ a i j, LinearMap.toMatrix b' b' ((T a).restrict (hS a)) i j =
        LinearMap.toMatrix b b (T a) (Fin.castSucc i) (Fin.castSucc j) := by
      intro a i j
      rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hr, hb']
      rfl
    refine ⟨b', fun a => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
    · exact (hm a i j).trans ((hb a).1 _ _ (Fin.castSucc_lt_castSucc_iff.2 hij))
    · exact (hm a i i).trans ((hb a).2 _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.WeilDeligne in
theorem UpperTheory.weil_group_dense_in_galois_group :
    UpperTheory.V.Af.Wd.WeilDense := by
  intro F Ω _ _ _ _ _ w A h
  have hσ := isFrob_frob (h := h)
  have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A w h ⟨_, hσ.1⟩ hσ
  have h2 : (Subgroup.zpowers (⟨_, hσ.1⟩ : Dec (F := F) A) ⊔
      (Ine (F := F) A).subgroupOf (Dec (F := F) A)) ≤ (Subgroup.inclusion (Weil_le_Dec h)).range := by
    refine sup_le ?_ fun x hx => ⟨⟨x, Ine_le_Weil h hx⟩, rfl⟩
    exact (Subgroup.zpowers_le).2 ⟨frob h, rfl⟩
  have h3 := Subgroup.topologicalClosure_mono h2
  rw [h1] at h3
  intro g
  exact h3 (Subgroup.mem_top g)
end

