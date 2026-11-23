module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNondegenerateTupleComplementFixer
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.FrameTuple

section Alg
variable {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {m : ℕ}

def tup (t : E) (g g' : Fin m → V) : Fin m ⊕ Fin m → V := Sum.elim g fun b => t • (g' b - g b)

theorem tup_indep {t θ : E} (h : θ * t = 1) {g g' : Fin m → V}
    (hli : LinearIndependent E (Sum.elim g g')) : LinearIndependent E (tup t g g') := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  have key := hli (Sum.elim (fun a => c (Sum.inl a) - t * c (Sum.inr a)) fun b => t * c (Sum.inr b))
    (by
      rw [← hc]
      simp only [Fintype.sum_sum_type, tup, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [sub_smul, smul_sub, smul_smul, mul_comm t]
      abel)
  have h2 : ∀ b, c (Sum.inr b) = 0 := fun b => by
    have := key (Sum.inr b)
    simp only [Sum.elim_inr] at this
    linear_combination θ * this - c (Sum.inr b) * h
  rintro (a | b)
  · have := key (Sum.inl a)
    simpa [h2] using this
  · exact h2 b

theorem tup_span {t θ : E} (h : θ * t = 1) (g g' : Fin m → V) :
    Submodule.span E (Set.range (tup t g g')) = Submodule.span E (Set.range (Sum.elim g g')) := by
  apply le_antisymm <;> rw [Submodule.span_le]
  · rintro _ ⟨a | b, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩)
        (Submodule.subset_span ⟨Sum.inl b, rfl⟩))
  · rintro _ ⟨a | b, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · have : Sum.elim g g' (Sum.inr b) = tup t g g' (Sum.inl b) + θ • tup t g g' (Sum.inr b) := by
        simp [tup, smul_smul, h]
      rw [this]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl b, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩))

theorem tup_change (t : E) (g g' p p' : Fin m → V) (u u' : Matrix (Fin m) (Fin m) E)
    (hp : ∀ j, p j = ∑ i, u i j • g i) (hp' : ∀ j, p' j = ∑ i, u' i j • g' i) (j) :
    tup t p p' j = ∑ i, (Matrix.fromBlocks u (t • (u' - u)) 0 u') i j • tup t g g' i := by
  rcases j with j | j
  · simp [tup, Fintype.sum_sum_type, hp]
  · simp only [tup, Fintype.sum_sum_type, hp, hp', Sum.elim_inl, Sum.elim_inr,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, Finset.smul_sum, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    module

theorem det_uni (s : Matrix (Fin m) (Fin m) E) (h0 : ∀ i j, j < i → s i j = 0) (h1 : ∀ i, s i i = 1) :
    s.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h0 i j hij)]
  simp [h1]

theorem comb_mul (g : Fin m → V) (s A : Matrix (Fin m) (Fin m) E) (j : Fin m) :
    ∑ i, A i j • ∑ l, s l i • g l = ∑ l, (s * A) l j • g l := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]

end Alg

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem gram_unit (L : LocE F E) [IsArtinianRing E] {n m : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (h : IsHerm L H) (x : Fin m → Fin n → E) (hli : LinearIndependent E x)
    (hd : Disjoint (Submodule.span E (Set.range x)) (perp L H (Submodule.span E (Set.range x)))) :
    IsUnit (gramT L H x).det := by
  have hinj : Function.Injective (Matrix.toLin' (gramT L H x)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro α hα
    have h1 : ∑ i, α i • x i = 0 := by
      refine Submodule.disjoint_def.1 hd _ ((Submodule.mem_span_range_iff_exists_fun E).2 ⟨α, rfl⟩) ?_
      rw [FrameBasic.mem_perp_span L h]
      intro j
      change FrameBasic.hfL L H (x j) _ = 0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Eq.trans ?_ (congrFun hα j)
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, gramT, Matrix.of_apply, map_smul,
        smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    funext i
    exact Fintype.linearIndependent_iff.1 hli α h1 i
  have hb := IsArtinian.bijective_of_injective_endomorphism _ hinj
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.isUnit_toLin'_iff]
  exact (Module.End.isUnit_iff _).2 hb

theorem isLat_std (L : LocE F E) (n : ℕ) :
    IsLat L (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : Fin n → E))) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨i, by simp⟩

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∃ x : Fin (2 * r + 2) → S.V, IsUnit (gramT L S.Hm x).det ∧ Submodule.span E (Set.range x) = S.ME ∧ S.H0 = fixG L S.Hm S.ME ∧ IsLat L (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))) ∧ (∀ Mh, S.massSig Mh = sigMass L S.Hm S.ME (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))) Mh) ∧ ∀ C, S.IsCls C → ∀ p ∈ C, ∃ (y : Fin (2 * r + 2) → S.V) (B : Matrix (Fin (2 * r + 2)) (Fin (2 * r + 2)) E), B.det * L.cj B.det = 1 ∧ y = rmul x B ∧ S.Mof p.1 p.2 = Submodule.span L.O (Set.range y) := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨hli, hco, -, -, -, hth, -⟩ := FrameBasic.main L r k S
  obtain ⟨hN, hN', -⟩ := FrameOnto.unipotent_onto L r k S
  let e : Fin (r + 1) ⊕ Fin (r + 1) ≃ Fin (2 * r + 2) := finSumFinEquiv.trans (finCongr (by omega))
  have hθ : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hth, map_one]
  have hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f')) := by
    have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
      ext i; simpa using i.2
    simp only [Frames.ME, Frames.spanTo, hs, Set.image_univ, Set.Sum.elim_range, Submodule.span_union]
  have hspan : Submodule.span E (Set.range (tup (algebraMap F E S.th⁻¹) S.f S.f' ∘ e.symm)) = S.ME := by
    rw [e.symm.surjective.range_comp, tup_span hθ, hME]
  refine ⟨tup (algebraMap F E S.th⁻¹) S.f S.f' ∘ e.symm, ?_, hspan, rfl, isLat_std L _, fun _ => rfl, ?_⟩
  · refine gram_unit L S.herm.1 _ ((tup_indep hθ hli).comp _ e.symm.injective) ?_
    rw [hspan]
    exact hco.disjoint
  · rintro C ⟨n, hn, n', hn', rfl⟩ p ⟨A, A', -, -, h0, h1, -, hp, hp'⟩
    obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := hN n hn
    obtain ⟨s', ⟨hs0', hs1'⟩, hs'⟩ := hN' n' hn'
    simp only [hs, hs', comb_mul] at hp hp'
    refine ⟨tup (algebraMap F E S.th⁻¹) p.1 p.2 ∘ e.symm,
      (Matrix.fromBlocks (s * A) (algebraMap F E S.th⁻¹ • (s' * A' - s * A)) 0 (s' * A')).submatrix
        e.symm e.symm, ?_, ?_, ?_⟩
    · rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul,
        det_uni s hs0 hs1, det_uni s' hs0' hs1', det_uni A (fun i j h => (h0 i j h).1) fun i => (h1 i).1,
        det_uni A' (fun i j h => (h0 i j h).2) fun i => (h1 i).2]
      simp
    · funext j
      rw [Function.comp_apply, tup_change _ S.f S.f' p.1 p.2 _ _ hp hp', rmul]
      exact (e.symm.sum_comp _).symm
    · rw [e.symm.surjective.range_comp, tup, Set.Sum.elim_range]
      rfl

end GlobalTheory.HL.FrameTuple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeGramDetAndMinorsOrbitInvariant
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FrameGram

theorem submatrix_mul_upper {E : Type} [CommRing E] {N m : ℕ} (hm : m ≤ N) {ι : Type} (f : ι → Fin N)
    (M B : Matrix (Fin N) (Fin N) E) (hB : ∀ i j, j < i → B i j = 0) :
    (M * B).submatrix f (Fin.castLE hm) =
      M.submatrix f (Fin.castLE hm) * B.submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hm) (Fin.castLE_injective hm) _ _ ?_ fun _ => rfl
  intro i hi
  rw [hB, mul_zero]
  by_contra h
  apply hi
  have h1 : (i : ℕ) ≤ b := not_lt.1 h
  exact ⟨⟨i, by omega⟩, rfl⟩

theorem det_sub_upper {E : Type} [CommRing E] {N m : ℕ} (hm : m ≤ N)
    (B : Matrix (Fin N) (Fin N) E) (hB : ∀ i j, j < i → B i j = 0) (h1 : ∀ i, B i i = 1) :
    (B.submatrix (Fin.castLE hm) (Fin.castLE hm)).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [h1]
  · intro i j hij
    exact hB _ _ hij

theorem lead_mul_upper {E : Type} [CommRing E] {N : ℕ} (M B : Matrix (Fin N) (Fin N) E)
    (hB : ∀ i j, j < i → B i j = 0) (h1 : ∀ i, B i i = 1) (l : Fin (N + 1)) :
    lead (M * B) l = lead M l := by
  unfold lead
  rw [submatrix_mul_upper _ _ _ _ hB, Matrix.det_mul, det_sub_upper _ _ hB h1, mul_one]

theorem lead_transpose {E : Type} [CommRing E] {N : ℕ} (M : Matrix (Fin N) (Fin N) E)
    (l : Fin (N + 1)) : lead M.transpose l = lead M l := by
  unfold lead
  rw [← Matrix.det_transpose]
  rfl

theorem lead_lower_mul {E : Type} [CommRing E] {N : ℕ} (M B : Matrix (Fin N) (Fin N) E)
    (hB : ∀ i j, j < i → B i j = 0) (h1 : ∀ i, B i i = 1) (l : Fin (N + 1)) :
    lead (B.transpose * M) l = lead M l := by
  rw [← lead_transpose, Matrix.transpose_mul, Matrix.transpose_transpose, lead_mul_upper _ _ hB h1,
    lead_transpose]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_sum_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι]
    (α : ι → E) (g : ι → Fin n → E) (y : Fin n → E) :
    hf L H (∑ i, α i • g i) y = ∑ i, α i * hf L H (g i) y := by
  change GlobalTheory.FrameBasic.hfL L H y _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl

theorem gram_change (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    {ι : Type} [Fintype ι] (u u' v v' : ι → Fin n → E) (P P' : Matrix ι ι E)
    (hv : ∀ j, v j = ∑ i, P i j • u i) (hv' : ∀ j, v' j = ∑ i, P' i j • u' i) :
    (Matrix.of fun a b => hf L H (v' b) (v a)) =
      (P.map L.cj).transpose * (Matrix.of fun a b => hf L H (u' b) (u a)) * P' := by
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hv', hf_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mul_comm, GlobalTheory.FrameBasic.hf_conj L h, hv, hf_sum_left, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← GlobalTheory.FrameBasic.hf_conj L h]

theorem det_conj (L : LocE F E) {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι E) :
    (A.map L.cj).transpose.det = L.cj A.det := by
  rw [Matrix.det_transpose]
  exact (AlgEquiv.map_det L.cj A).symm

theorem span_frames {V : Type} [AddCommGroup V] [Module E V] {ι : Type} (g g' : ι → V) (t : F)
    (ht : t ≠ 0) :
    Submodule.span E (Set.range (Sum.elim g fun i => algebraMap F E t⁻¹ • (g' i - g i))) =
      Submodule.span E (Set.range g) ⊔ Submodule.span E (Set.range g') := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i | i, rfl⟩
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩))
        (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)))
  · rw [sup_le_iff, Submodule.span_le, Submodule.span_le]
    constructor
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    · rintro _ ⟨i, rfl⟩
      have e : g' i = algebraMap F E t • (algebraMap F E t⁻¹ • (g' i - g i)) + g i := by
        rw [smul_smul, ← map_mul, mul_inv_cancel₀ ht, map_one, one_smul, sub_add_cancel]
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
        (Submodule.subset_span ⟨Sum.inl i, rfl⟩)

theorem vE_const [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) (r k : ℕ)
    (S : Frames L r k) (c : F) (hc : c ≠ 0) (m : ℕ) :
    vE L S.ϖ (algebraMap F E ((-1) ^ (r + 1) * c * S.th⁻¹ ^ m)) =
      vE L S.ϖ (algebraMap F E c) - m * S.vth := by
  obtain ⟨hadd, hϖ, -, -⟩ := GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr
  have hth : S.th ≠ 0 := (GlobalTheory.FrameBasic.main L r k S).2.2.2.2.2.1
  have h1 : vE L S.ϖ (algebraMap F E 1) = 0 := by
    have := hadd 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega
  have hn : vE L S.ϖ (algebraMap F E (-1)) = 0 := by
    have := hadd (-1) (-1) (by simp) (by simp)
    rw [neg_mul_neg, mul_one] at this
    omega
  have ht : vE L S.ϖ (algebraMap F E S.th) = S.vth := by
    unfold Frames.th Frames.vth
    split_ifs
    · exact hϖ
    · exact h1
  have hti : vE L S.ϖ (algebraMap F E S.th⁻¹) = -S.vth := by
    have := hadd S.th S.th⁻¹ hth (inv_ne_zero hth)
    rw [mul_inv_cancel₀ hth] at this
    omega
  have hpow : ∀ x : F, x ≠ 0 → ∀ j : ℕ,
      vE L S.ϖ (algebraMap F E (x ^ j)) = j * vE L S.ϖ (algebraMap F E x) := by
    intro x hx j
    induction j with
    | zero => rw [pow_zero, h1]; simp
    | succ j ih => rw [pow_succ, hadd _ _ (pow_ne_zero _ hx) hx, ih]; push_cast; ring
  rw [hadd _ _ (mul_ne_zero (pow_ne_zero _ (by simp)) hc) (pow_ne_zero _ (inv_ne_zero hth)),
    hadd _ _ (pow_ne_zero _ (by simp)) hc, hpow _ (by simp), hpow _ (inv_ne_zero hth), hn, hti]
  ring

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∀ n' ∈ S.N', (∃ c : F, c ≠ 0 ∧ vE L S.ϖ (algebraMap F E c) = S.a ∧ (Matrix.of fun a b => S.h (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))) b) (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))) a)).det = algebraMap F E c) ∧ (∀ l, lead (Matrix.of fun a b => S.h (n' (S.f' b)) (n (S.f a))) l = S.D l) ∧ Submodule.span E (Set.range (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))))) = S.ME := by
  intro F _ _ _ _ _ E _ _ _ L r k S n hn n' hn'
  obtain ⟨⟨s, ⟨hs0, hs1⟩, hs⟩, hsp, -⟩ := (GlobalTheory.HL.frame_unipotent_unitriangular L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩)).2 n hn
  obtain ⟨⟨s', ⟨hs0', hs1'⟩, hs'⟩, hsp', -⟩ :=
    (GlobalTheory.HL.frame_unipotent_unitriangular L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩)).2 n' hn'
  obtain ⟨-, -, ⟨c, hc0, hc⟩, -, -, hth, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hlead : ∀ l, lead (Matrix.of fun a b => S.h (n' (S.f' b)) (n (S.f a))) l = S.D l := by
    intro l
    have e := gram_change L S.herm.1 S.f S.f' _ _ s s' hs hs'
    unfold Frames.h
    rw [e, lead_mul_upper _ _ hs0' hs1', lead_lower_mul]
    · rfl
    · intro i j hij; rw [Matrix.map_apply, hs0 i j hij, map_zero]
    · intro i; rw [Matrix.map_apply, hs1, map_one]
  refine ⟨⟨(-1) ^ (r + 1) * c * S.th⁻¹ ^ (2 * (r + 1)),
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) hc0) (pow_ne_zero _ (inv_ne_zero hth)),
    ?_, ?_⟩, hlead, ?_⟩
  · rw [vE_const L r k S c hc0, Frames.a, hc]
    push_cast; ring
  · set Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
      Matrix.of fun a b => S.h (n' (S.f' b)) (n (S.f a)) with hZ
    set t : E := algebraMap F E S.th⁻¹ with ht
    let P : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      Matrix.fromBlocks 1 (Matrix.diagonal fun _ => -t) 0 (Matrix.diagonal fun _ => t)
    have hP : ∀ j, (Sum.elim (fun i => n (S.f i)) (fun i => t • (n' (S.f' i) - n (S.f i)))) j =
        ∑ i, P i j • (Sum.elim (fun i => n (S.f i)) (fun i => n' (S.f' i))) i := by
      rintro (j | j)
      · simp [P, Fintype.sum_sum_type, Matrix.one_apply]
      · simp [P, Fintype.sum_sum_type, Matrix.diagonal_apply, smul_sub]
        abel
    have hPd : P.det = t ^ (r + 1) := by
      simp [P, Matrix.det_fromBlocks_zero₂₁]
    have e := gram_change L S.herm.1 _ _ _ _ P P hP hP
    have hG : (Matrix.of fun a b => hf L S.Hm
        ((Sum.elim (fun i => n (S.f i)) (fun i => n' (S.f' i))) b)
        ((Sum.elim (fun i => n (S.f i)) (fun i => n' (S.f' i))) a)) =
        Matrix.fromBlocks (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E S.T))) Z
          (Z.map L.cj).transpose
          (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E S.T'))) := by
      ext (a | a) (b | b)
      · have := hn.1.1 (S.f b) (S.f a)
        simp only [Matrix.of_apply, Sum.elim_inl, Matrix.fromBlocks_apply₁₁, this, S.gram,
          Matrix.single_apply, eq_comm, and_comm]
      · rfl
      · exact GlobalTheory.FrameBasic.hf_conj L S.herm.1 _ _
      · have := hn'.1.1 (S.f' b) (S.f' a)
        simp only [Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, this, S.gram',
          Matrix.single_apply, eq_comm, and_comm]
    have hD1 : Z.det = S.D (Fin.last (r + 1)) := hlead (Fin.last (r + 1))
    have hD0 : (Z.submatrix Fin.castSucc Fin.castSucc).det = S.D (Fin.last r).castSucc :=
      hlead (Fin.last r).castSucc
    have e2 : ((Z.map L.cj).transpose.submatrix Fin.castSucc Fin.castSucc) =
      ((Z.submatrix Fin.castSucc Fin.castSucc).map L.cj).transpose := rfl
    have hct : L.cj t = t := L.cj.commutes _
    unfold Frames.h
    rw [e, Matrix.det_mul, Matrix.det_mul, det_conj, hPd, hG, GlobalTheory.HL.det_gram_two_frames, e2,
      det_conj, det_conj, hD1, hD0, ← map_mul (algebraMap F E), map_pow, hct]
    change _ * (_ * S.G) * _ = _
    rw [hc, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, ← ht]
    ring
  · have hu : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
      ext i; simpa using i.2
    rw [span_frames _ _ _ hth, Frames.ME, ← hsp, ← hsp']
    simp only [Frames.spanTo, hu, Set.image_univ]

end GlobalTheory.FrameGram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentOfGram
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.OverBasis

open Matrix GlobalTheory.HL.SelfDual

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_comb (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin m → Fin n → E)
    (c : Fin m → E) : (fun a => hf L Hm (∑ b, c b • y b) (y a)) = gramT L Hm y *ᵥ c := by
  funext a
  rw [hf_sum_l]
  simp [gramT, Matrix.mulVec, dotProduct, mul_comm]

theorem linearIndependent_of_gram (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (y : Fin m → Fin n → E) (h : IsUnit (gramT L Hm y).det) : LinearIndependent E y := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 := hf_comb L Hm y c
  rw [hc] at h1
  have h2 : gramT L Hm y *ᵥ c = 0 := by
    rw [← h1]; funext a; simp [hf]
  have h3 : (gramT L Hm y)⁻¹ *ᵥ (gramT L Hm y *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
  rw [h2, Matrix.mulVec_zero] at h3
  exact fun i => congrFun h3.symm i

omit [TopologicalSpace E] in
theorem sum_smul_rmul {n m : ℕ} (y : Fin m → Fin n → E) (B : Matrix (Fin m) (Fin m) E)
    (c : Fin m → E) : ∑ j, c j • rmul y B j = ∑ i, (B *ᵥ c) i • y i := by
  simp only [rmul, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem exists_basis_overlattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (y : Fin m → Fin n → E), IsUnit (gramT L Hm y).det → ∀ Mh : Submodule L.O (Fin n → E), Submodule.span L.O (Set.range y) ≤ Mh → (∀ v ∈ Mh, v ∈ Submodule.span E (Set.range y)) → (∀ v ∈ Mh, ∀ w ∈ Mh, hf L Hm v w ∈ L.O) → LinearIndependent E y ∧ ∃ A : Matrix (Fin m) (Fin m) E, IsIntM L A ∧ IsUnit A.det ∧ Mh = Submodule.span L.O (Set.range (rmul y A⁻¹)) ∧ LinearIndependent E (rmul y A⁻¹) ∧ rmul (rmul y A⁻¹) A = y := by
  intro F _ _ _ _ _ E _ _ _ L n Hm _ m y hG Mh hy hsp hint
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hP : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  have hli := linearIndependent_of_gram L Hm y hG
  refine ⟨hli, ?_⟩
  have hyM : ∀ a, y a ∈ Mh := fun a => hy (Submodule.subset_span ⟨a, rfl⟩)
  let f : (Fin m → L.O) →ₗ[L.O] (Fin n → E) :=
    { toFun := fun w => ∑ i, ((gramT L Hm y)⁻¹ *ᵥ fun a => (w a : E)) i • y i
      map_add' := fun v w => by
        have : (fun a => ((v + w) a : E)) = (fun a => (v a : E)) + fun a => (w a : E) := rfl
        rw [this, Matrix.mulVec_add]
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        have : (fun a => ((c • v) a : E)) = (c : E) • fun a => (v a : E) := rfl
        rw [this, Matrix.mulVec_smul, RingHom.id_apply, Subring.smul_def, Finset.smul_sum]
        simp only [Pi.smul_apply, smul_assoc] }
  have hle : Mh ≤ LinearMap.range f := by
    intro v hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 (hsp v hv)
    refine ⟨fun a => ⟨_, hint _ hv _ (hyM a)⟩, ?_⟩
    show ∑ i, ((gramT L Hm y)⁻¹ *ᵥ fun a => hf L Hm (∑ b, c b • y b) (y a)) i • y i = _
    rw [hf_comb, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]
  obtain ⟨b, hb⟩ := exists_eq_span_range m (Mh.comap f)
  let B : Matrix (Fin m) (Fin m) E :=
    Matrix.of fun i j => ((gramT L Hm y)⁻¹ *ᵥ fun a => (b j a : E)) i
  have hM : Mh = Submodule.span L.O (Set.range (rmul y B)) := by
    rw [← Submodule.map_comap_eq_of_le hle, hb, Submodule.map_span, ← Set.range_comp]
    rfl
  have hA : ∀ j, ∃ c : Fin m → L.O, ∑ i, c i • rmul y B i = y j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun L.O).1 (hM ▸ hyM j)
  choose c hc using hA
  let A : Matrix (Fin m) (Fin m) E := Matrix.of fun i j => (c j i : E)
  have hA : rmul (rmul y B) A = y := funext hc
  have hBA : B * A = 1 := by
    ext i j
    have h1 : ∑ i, (B *ᵥ fun k => A k j) i • y i = y j := by
      rw [← sum_smul_rmul]; exact hc j
    have h2 : ∑ i, ((B *ᵥ fun k => A k j) - (Pi.single j 1 : Fin m → E)) i • y i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1]
      simp [Pi.single_apply]
    have h3 := sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h2 i)
    rw [Matrix.one_apply, ← Pi.single_apply, ← h3]
    rfl
  have hinv : A⁻¹ = B := Matrix.inv_eq_left_inv hBA
  refine ⟨A, fun i j => (c j i).2, Matrix.isUnit_det_of_left_inverse hBA, ?_⟩
  rw [hinv]
  refine ⟨hM, ?_, hA⟩
  rw [Fintype.linearIndependent_iff]
  intro d hd
  rw [sum_smul_rmul] at hd
  have h1 : B *ᵥ d = 0 := funext (Fintype.linearIndependent_iff.1 hli _ hd)
  have h2 : A *ᵥ (B *ᵥ d) = d := by
    rw [Matrix.mulVec_mulVec, mul_eq_one_comm.1 hBA, Matrix.one_mulVec]
  rw [h1, Matrix.mulVec_zero] at h2
  exact fun i => congrFun h2.symm i

end GlobalTheory.HL.OverBasis
end

