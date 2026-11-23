module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsDimX
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace FlagHeightMultilinear

theorem exists_perm_toList {α : Type} [DecidableEq α] {d : ℕ} (r : Fin d → α) :
    ∃ σ : Equiv.Perm (Fin d), ∀ (k : Fin d) (h : (k : ℕ) < (Multiset.map r Finset.univ.val).toList.length),
      (Multiset.map r Finset.univ.val).toList.get ⟨k, h⟩ = r (σ k) := by
  set l := (Multiset.map r Finset.univ.val).toList with hl
  have hlen : l.length = d := by simp [hl, Multiset.length_toList]
  let r' : Fin d → α := fun k => l.get ⟨k, by rw [hlen]; exact k.2⟩
  have hmap : Multiset.map r' Finset.univ.val = Multiset.map r Finset.univ.val := by
    rw [Fin.univ_val_map]
    have hof : List.ofFn r' = l := List.ext_get (by simp [hlen]) (fun k h1 h2 => by simp [r'])
    rw [hof, hl, Multiset.coe_toList]
  have hcard : ∀ a, Fintype.card {k // r' k = a} = Fintype.card {k // r k = a} := by
    intro a
    have h := congrArg (Multiset.count a) hmap
    rw [Multiset.count_map, Multiset.count_map] at h
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    convert h using 3 <;> exact eq_comm
  refine ⟨Equiv.ofFiberEquiv (fun a => Fintype.equivOfCardEq (hcard a)), fun k h => ?_⟩
  exact (Equiv.ofFiberEquiv_map (fun a => Fintype.equivOfCardEq (hcard a)) k).symm

section FS

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isSmoothHerm_fsHerm (a : K → ℤ) : IsSmoothHerm (fsHerm ι a) := by
  have h := Inter.isSmoothHerm_ofMetrics_fs (ι := ι) a
  unfold IsSmoothHerm at h ⊢
  refine h.congr fun z _ => ?_
  rw [fsHerm_h, Inter.ofMetrics_fs_h]
  unfold refNorm
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← sq_rpow_half (Real.sqrt_nonneg _) (a k),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem refNorm_mul {a b : K → ℤ} {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    refNorm a z * refNorm b z = refNorm (a + b) z := by
  unfold refNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  obtain ⟨i, hi⟩ := hz k
  have hpos : 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 :=
    Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  rw [← Real.rpow_add hpos]
  congr 1
  simp only [Pi.add_apply, Int.cast_add]
  ring

variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem I_snoc_congr (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (ha : A.a = B.a) (hh : ∀ z ∈ mcPts P, A.h z = B.h z) :
    I P (n + 1) (Fin.snoc L A) = I P (n + 1) (Fin.snoc L B) := by
  have hBi := Inter.isSmoothHerm_hermZpow hB (-1)
  have h0 := Inter.DiagRAux.I_snoc_triv hI hP hL (Inter.isSmoothHerm_tensor hA hBi)
    (by
      show A.a + (Inter.hermZpow B (-1)).a = 0
      rw [Inter.DiagRAux.hermZpow_neg_one_a, ha, add_neg_cancel])
    (fun z hz => by
      show A.h z * (Inter.hermZpow B (-1)).h z = 1
      rw [Inter.DiagRAux.hermZpow_neg_one_h, hh z hz, mul_inv_cancel₀ (B.pos z hz.1).ne'])
  have h1 := hI.2.1 P n L A (Inter.hermZpow B (-1)) hP hL hA hBi
  have h2 := Inter.fam_snoc_zpow hI hP L hL hB (-1)
  rw [h0, h2] at h1
  push_cast at h1
  linarith

theorem I_snoc_fsHerm_add (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) (a b : K → ℤ) :
    I P (n + 1) (Fin.snoc L (fsHerm ι (a + b))) =
      I P (n + 1) (Fin.snoc L (fsHerm ι a)) + I P (n + 1) (Fin.snoc L (fsHerm ι b)) := by
  rw [← hI.2.1 P n L _ _ hP hL (isSmoothHerm_fsHerm a) (isSmoothHerm_fsHerm b)]
  exact I_snoc_congr hI hP L hL (isSmoothHerm_fsHerm _)
    (Inter.isSmoothHerm_tensor (isSmoothHerm_fsHerm a) (isSmoothHerm_fsHerm b)) rfl
    (fun z hz => (refNorm_mul hz.1).symm)

theorem I_update_fsHerm_add (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (v : Fin (n + 1) → K → ℤ) (j : Fin (n + 1)) (a b : K → ℤ) :
    I P (n + 1) (fun i => fsHerm ι (Function.update v j (a + b) i)) =
      I P (n + 1) (fun i => fsHerm ι (Function.update v j a i)) +
        I P (n + 1) (fun i => fsHerm ι (Function.update v j b i)) := by
  have hL : ∀ i, IsSmoothHerm (fsHerm ι (v i)) := fun i => isSmoothHerm_fsHerm _
  have e : ∀ c : K → ℤ, (fun i => fsHerm ι (Function.update v j c i)) =
      Function.update (fun i => fsHerm ι (v i)) j (fsHerm ι c) := by
    intro c
    funext i
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [Function.update_of_ne h]
  rw [e, e, e, Inter.fam_update_eq_snoc hI hP _ hL j (isSmoothHerm_fsHerm _),
    Inter.fam_update_eq_snoc hI hP _ hL j (isSmoothHerm_fsHerm _),
    Inter.fam_update_eq_snoc hI hP _ hL j (isSmoothHerm_fsHerm _)]
  exact I_snoc_fsHerm_add hI hP _ (fun i => hL _) a b

def fsMultilin (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) :
    MultilinearMap (RingHom.id ℤ) (fun _ : Fin (n + 1) => K → ℤ) ℝ where
  toFun v := I P (n + 1) (fun i => fsHerm ι (v i))
  map_update_add' := by
    intro inst v j a b
    have e : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    subst e
    exact I_update_fsHerm_add hI hP v j a b
  map_update_smul' := by
    intro inst v j c a
    have e : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    subst e
    let g : (K → ℤ) →+ ℝ := AddMonoidHom.mk' (fun a => I P (n + 1) (fun i => fsHerm ι (Function.update v j a i)))
      (fun a b => I_update_fsHerm_add hI hP v j a b)
    exact map_zsmul g c a

theorem fsMultilin_apply (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) (v : Fin (n + 1) → K → ℤ) :
    fsMultilin hI hP v = I P (n + 1) (fun i => fsHerm ι (v i)) := rfl

theorem I_fsHerm_sum (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {α : Type} [Fintype α]
    (ℓ : Fin (n + 1) → α → ℤ) (x : α → K → ℤ) :
    I P (n + 1) (fun i => fsHerm ι (∑ p, ℓ i p • x p)) =
      ∑ r : Fin (n + 1) → α, (∏ i, (ℓ i (r i) : ℝ)) * I P (n + 1) (fun i => fsHerm ι (x (r i))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← fsMultilin_apply hI hP, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ (fsMultilin hI hP) (fun i => ℓ i (r i)) (fun i => x (r i)),
    fsMultilin_apply]
  simp only [RingHom.id_apply, zsmul_eq_mul, Int.cast_prod]

end FS

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

theorem hFl_sum_monomial (II : IntersectionSystem) {β : Type} (s : Finset β) (m : β → (Ψ × Fin N) →₀ ℕ)
    (a : β → ℚ) :
    hFl Ψ N II (∑ b ∈ s, monomial (m b) (a b)) = ∑ b ∈ s, (a b : ℝ) * hFlMono Ψ N II (m b) := by
  classical
  have hsub : ∀ (F : RootPoly Ψ N) (S : Finset ((Ψ × Fin N) →₀ ℕ)), F.support ⊆ S →
      hFl Ψ N II F = ∑ m ∈ S, ((AddMonoidAlgebra.coeff F m : ℚ) : ℝ) * hFlMono Ψ N II m := by
    intro F S hS
    unfold hFl
    exact Finset.sum_subset hS fun m _ hm => by rw [notMem_support_iff.mp hm]; simp
  have hadd : ∀ F G : RootPoly Ψ N, hFl Ψ N II (F + G) = hFl Ψ N II F + hFl Ψ N II G := by
    intro F G
    rw [hsub (F + G) (F.support ∪ G.support) support_add,
      hsub F (F.support ∪ G.support) Finset.subset_union_left,
      hsub G (F.support ∪ G.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_add]
    push_cast
    ring
  have hmono : ∀ (m : (Ψ × Fin N) →₀ ℕ) (a : ℚ), hFl Ψ N II (monomial m a) = (a : ℝ) * hFlMono Ψ N II m := by
    intro m a
    rw [hsub _ {m} support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]
  induction s using Finset.induction_on with
  | empty => simp [hsub 0 ∅ (by simp)]
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, hadd, hmono, ih]


omit [DecidableEq Ψ] in
theorem C_mul_prod_linForm (c : ℚ) {d : ℕ} (ℓ : Fin d → Ψ × Fin N → ℤ) :
    (C c * ∏ i, linForm Ψ N (ℓ i) : RootPoly Ψ N) =
      ∑ r : Fin d → Ψ × Fin N, monomial (∑ i, Finsupp.single (r i) 1) (c * ∏ i, (ℓ i (r i) : ℚ)) := by
  unfold linForm
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← C_mul_monomial]
  congr 1
  rw [show (∏ i, (ℓ i (r i) : ℚ)) = (∏ i, (ℓ i (r i) : ℚ)) * 1 from (mul_one _).symm, ← C_mul_monomial,
    monomial_sum_one]
  simp only [smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]
  rfl

theorem hFlMono_sum_single (II : IntersectionSystem) (hII : IsIntersectionSystem II)
    (hP : IsArithVar (PFl Ψ N) (dimFl Ψ N + 1)) (r : Fin (dimFl Ψ N + 1) → Ψ × Fin N) :
    hFlMono Ψ N II (∑ i, Finsupp.single (r i) 1) =
      II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (fun i => xLine Ψ N (r i)) := by
  have hdeg : (∑ i, Finsupp.single (r i) (1 : ℕ)).degree = dimFl Ψ N + 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp [Finsupp.degree_single]
  have hm : Finsupp.toMultiset (∑ i, Finsupp.single (r i) (1 : ℕ)) = Multiset.map r Finset.univ.val := by
    rw [Finsupp.toMultiset_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    rw [Finset.sum_eq_multiset_sum]
    have e : (fun i => ({r i} : Multiset (Ψ × Fin N))) = (fun p => {p}) ∘ r := rfl
    rw [e, ← Multiset.map_map, Multiset.sum_map_singleton]
  obtain ⟨σ, hσ⟩ := exists_perm_toList r
  have hML : monoLines Ψ N (∑ i, Finsupp.single (r i) 1) (dimFl Ψ N + 1) = (fun i => xLine Ψ N (r i)) ∘ σ := by
    funext k
    have hk : (k : ℕ) < (Multiset.map r Finset.univ.val).toList.length := by
      have := k.2
      simp [Multiset.length_toList]
      omega
    unfold monoLines
    rw [hm, dite_eq_left hk, hσ k hk]
    rfl
  unfold hFlMono
  rw [if_pos hdeg, hML]
  exact (hII (FlBlock Ψ N) (FlIdx Ψ N)).1 _ _ _ σ hP fun j => isSmoothHerm_fsHerm _

end FlagHeightMultilinear


open FlagHeightMultilinear in
theorem HFlProdLinear.proof (hA : FlagArithVar.Statement) : HFlProdLinear.Statement := by
  intro II Ψ _ _ _ N d c ℓ hII hN hd
  subst hd
  have hP := hA Ψ N hN
  have hI := hII (FlBlock Ψ N) (FlIdx Ψ N)
  rw [C_mul_prod_linForm, hFl_sum_monomial]
  have hlin : (fun i => linLine Ψ N (ℓ i)) =
      fun i => fsHerm (FlIdx Ψ N) (∑ p, ℓ i p • xDeg Ψ N p) := by
    funext i
    unfold linLine linDeg
    congr 1
    funext q
    simp [Finset.sum_apply]
  rw [hlin, I_fsHerm_sum hI hP, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hFlMono_sum_single Ψ N II hII hP r]
  simp only [xLine]
  push_cast
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagNeZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem HodgeFlagNeZero.proof : HodgeFlagNeZero.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B τ i
  classical

  let BE : Module.Basis (Fin D.N) Ω (E τ) := Module.Basis.mk (B.e_indep τ) (B.e_span τ).ge
  let w : ⋀[Ω]^((i : ℕ) + 1) (E τ) := exteriorPower.ιMulti Ω _ (B.e τ ∘ Fin.castLE (step_le i))
  have hw : w ≠ 0 := by
    have h := (BE.exteriorPower ((i : ℕ) + 1)).ne_zero
      (Set.powersetCard.ofFinEmbEquiv (Fin.castLEOrderEmb (step_le i)))
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, Equiv.symm_apply_apply] at h
    convert h using 2
    funext x
    simp [BE, Fin.castLEOrderEmb]

  choose cX hcX using D.arith.2.1.2.2
  have hy : ∀ k, D.y ⟨k, cX k⟩ ≠ 0 := by
    intro k h0
    apply hcX k
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
  have hseg : segreCoord D.y cX ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  obtain ⟨M, f, cc, -, -, hsum, hPr⟩ := Pl.generates τ i cX hseg
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      simp at hsum
    · exact h
  obtain ⟨b, -, hbspan, hA⟩ := hPr ⟨0, hM⟩
  have : Module.Finite Ω (E τ) := Module.Finite.of_basis BE
  have hbi : LinearIndependent Ω b :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hbspan.ge
      (by rw [Module.finrank_eq_card_basis BE])
  let Bw := (Module.Basis.mk hbi hbspan.ge).exteriorPower ((i : ℕ) + 1)

  have hm : ∃ m, Pl.gen τ i m w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw
    refine Bw.forall_coord_eq_zero_iff.1 fun t => ?_
    obtain ⟨a, -, ha⟩ := hA _ (Set.powersetCard.ofFinEmbEquiv.symm t).strictMono
    let ψ : Module.Dual Ω (⋀[Ω]^((i : ℕ) + 1) (E τ)) :=
      ∑ m, (a m * chartMono D.y cX (-Pl.bdeg τ i)) • Pl.gen τ i m
    have hψ : ψ = Bw.coord t := by
      refine Bw.ext fun u => ?_
      have h1 := ha _ (Set.powersetCard.ofFinEmbEquiv.symm u).strictMono
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      simp only [Bw, exteriorPower.basis_apply, exteriorPower.ιMulti_family, ψ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Module.Basis.coe_mk]
      calc ∑ m, a m * chartMono D.y cX (-Pl.bdeg τ i) * Pl.gen τ i m (exteriorPower.ιMulti Ω _
              (b ∘ Set.powersetCard.ofFinEmbEquiv.symm u))
          = ∑ m, a m * (Pl.gen τ i m (exteriorPower.ιMulti Ω _
              (b ∘ Set.powersetCard.ofFinEmbEquiv.symm u)) * chartMono D.y cX (-Pl.bdeg τ i)) :=
            Finset.sum_congr rfl fun m _ => by ring
        _ = _ := h1
        _ = _ := by
          by_cases htu : t = u
          · subst htu
            simp
          · rw [if_neg fun h' =>
              htu (Set.powersetCard.ofFinEmbEquiv.symm.injective (DFunLike.coe_injective h')).symm]
            simp [Ne.symm htu]
    rw [← hψ]
    simp [ψ, hcon]
  obtain ⟨m0, hm0⟩ := hm

  refine ⟨m0, ?_⟩
  let c0 : Fin ((i : ℕ) + 1) → Fin D.N := Fin.castLE (step_le i)
  let v : (Fin ((i : ℕ) + 1) → Fin D.N) → Fin ((i : ℕ) + 1) → Ψ × Fin D.N × Fin D.N :=
    fun c a => (τ, headIdx (step_le i) a, c a)
  let μ : (Fin ((i : ℕ) + 1) → Fin D.N) → (Ψ × Fin D.N × Fin D.N) →₀ ℕ :=
    fun c => ∑ a, Finsupp.single (v c a) 1
  let g : (Fin ((i : ℕ) + 1) → Fin D.N) → Ω :=
    fun c => Pl.gen τ i m0 (exteriorPower.ιMulti Ω _ (B.e τ ∘ c))
  let z : (Fin ((i : ℕ) + 1) → Fin D.N) → Ω := fun c =>
    ∏ a, if ((headIdx (step_le i) a : ℕ) < D.j ∧ D.j ≤ (c a : ℕ)) then 0 else 1
  let P : MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω := ∑ c, monomial (μ c) (z c * g c)
  have hP : Pl.pluecker0 B τ i m0 = algebraMap _ Pl.ΩY P := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [PlueckerData.pluecker0, PlueckerData.gvar0, PlueckerData.gvar, PlueckerData.ofΩ, P, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hfac : ∀ a, (if ((headIdx (step_le i) a : ℕ) < D.j ∧ D.j ≤ (c a : ℕ)) then (0 : Pl.ΩY)
        else algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (X (τ, headIdx (step_le i) a, c a))) =
        algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY
          (C (if ((headIdx (step_le i) a : ℕ) < D.j ∧ D.j ≤ (c a : ℕ)) then 0 else 1) *
            X (τ, headIdx (step_le i) a, c a)) := by
      intro a
      split_ifs <;> simp
    rw [Finset.prod_congr rfl fun a _ => hfac a, ← map_prod, ← map_mul]
    congr 1
    rw [show monomial (μ c) (z c * g c) = C (z c * g c) * monomial (μ c) 1 by rw [C_mul_monomial, mul_one],
      monomial_sum_one, Finset.prod_mul_distrib]
    simp only [z, g, map_mul, map_prod, v, MvPolynomial.X]
    ring
  have hμ : ∀ c, μ c = μ c0 → c = c0 := by
    intro c h
    funext a
    have h2 := congrArg (fun φ : (Ψ × Fin D.N × Fin D.N) →₀ ℕ => φ (τ, headIdx (step_le i) a, c0 a)) h
    simp only [μ, v, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Prod.mk.injEq,
      true_and, headIdx, Fin.castLE_inj] at h2
    rw [Finset.sum_eq_single a (fun a' _ h' => if_neg fun h'' => h' h''.1) (by simp),
      Finset.sum_eq_single a (fun a' _ h' => if_neg fun h'' => h' h''.1) (by simp)] at h2
    by_contra hne
    simp [hne] at h2
  have hz : z c0 = 1 :=
    Finset.prod_eq_one fun a _ => if_neg fun h => lt_irrefl _ (h.1.trans_le h.2)
  have hcoeff : AddMonoidAlgebra.coeff P (μ c0) = g c0 := by
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single c0 (fun c _ hc => if_neg fun h => hc (hμ c h)) (by simp), if_pos rfl, hz, one_mul]
  have hPne : P ≠ 0 := fun h => hm0 (by simpa [h, g, c0, w] using hcoeff.symm)
  rw [hP]
  exact fun h => hPne (IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY
    (by rw [h, map_zero]))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.RingKrullDimLocalizationInt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Algebra MvPolynomial TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar)

theorem DimX.ringKrullDim_localization_int (B : Type) [CommRing B] [IsDomain B]
    [inst : Algebra ℤ B] [Algebra.FiniteType ℤ B] (hinj : Function.Injective (algebraMap ℤ B)) (t : ℕ)
    (ht : trdeg ℤ B = t) :
    ringKrullDim (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ))) = t := by
  obtain rfl : inst = Ring.toIntAlgebra B := Subsingleton.elim _ _
  let : Algebra B (ℚ ⊗[ℤ] B) := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)
  have hM : M ≤ nonZeroDivisors B := by
    rintro _ ⟨m, hm, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    exact nonZeroDivisors.ne_zero hm (hinj (h.trans (map_zero _).symm))
  have : IsLocalization M (ℚ ⊗[ℤ] B) := IsLocalization.tensorRight _ _
  have : IsDomain (ℚ ⊗[ℤ] B) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM

  have hBL : Function.Injective (algebraMap B (ℚ ⊗[ℤ] B)) := IsLocalization.injective _ hM
  have : FaithfulSMul B (ℚ ⊗[ℤ] B) := (faithfulSMul_iff_algebraMap_injective _ _).2 hBL
  have : FaithfulSMul ℤ B := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : FaithfulSMul ℤ ℚ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap ℤ ℚ).injective_int
  have : FaithfulSMul ℚ (ℚ ⊗[ℤ] B) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap ℚ (ℚ ⊗[ℤ] B)).injective
  have := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int (algebraMap ℤ (ℚ ⊗[ℤ] B))
    ((algebraMap B (ℚ ⊗[ℤ] B)).comp (algebraMap ℤ B)))
  have := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int (algebraMap ℤ (ℚ ⊗[ℤ] B))
    ((algebraMap ℚ (ℚ ⊗[ℤ] B)).comp (algebraMap ℤ ℚ)))
  have : Algebra.IsAlgebraic B (ℚ ⊗[ℤ] B) := IsLocalization.isAlgebraic _ M
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have h1 := trdeg_add_eq ℤ B (A := ℚ ⊗[ℤ] B)
  have h2 := trdeg_add_eq ℤ ℚ (A := ℚ ⊗[ℤ] B)
  rw [trdeg_eq_zero (R := B) (A := ℚ ⊗[ℤ] B), add_zero] at h1
  rw [trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add] at h2
  have htL : trdeg ℚ (ℚ ⊗[ℤ] B) = t := by rw [h2, ← h1, ht]

  rw [← ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field (K := ℚ) (A := ℚ ⊗[ℤ] B) t htL]
  exact ringKrullDim_eq_of_ringEquiv
    (IsLocalization.algEquiv M (Localization M) (ℚ ⊗[ℤ] B)).toRingEquiv

theorem DimX.proof : DimX.Statement := by
  intro K _ ι _ P n hP
  obtain ⟨-, ⟨hPp, -, -⟩, hhor, hdim⟩ := hP
  have := hPp

  have hinj : Function.Injective (algebraMap ℤ (MRing ι ⧸ P)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro m hm
    have hm' : m ∈ P.comap (C : ℤ →+* MRing ι) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, ← hm]
      exact congrArg (fun f : ℤ →+* MRing ι ⧸ P => f m)
        (RingHom.ext_int ((Ideal.Quotient.mk P).comp C) (algebraMap ℤ (MRing ι ⧸ P)))
    rw [hhor, Ideal.mem_bot] at hm'
    exact hm'

  have : Algebra.FiniteType ℤ (MRing ι ⧸ P) :=
    .of_surjective (Ideal.Quotient.mkₐ ℤ P) (Ideal.Quotient.mkₐ_surjective ℤ P)
  have hfin : trdeg ℤ (MRing ι ⧸ P) < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.mp hfin
  have hB := IntDomainDim.proof (MRing ι ⧸ P) hinj
  rw [ht, Cardinal.toENat_nat, hdim] at hB
  have htn : t = n + Fintype.card K := by
    have h1 : ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) = ((t + 1 : ℕ) : WithBot ℕ∞) := by
      exact_mod_cast hB
    have h2 : n + 1 + Fintype.card K = t + 1 := by exact_mod_cast h1
    omega
  rw [← htn]
  exact DimX.ringKrullDim_localization_int (MRing ι ⧸ P) hinj t ht

end GroundTheory.Heights₂.Heights
end
end

