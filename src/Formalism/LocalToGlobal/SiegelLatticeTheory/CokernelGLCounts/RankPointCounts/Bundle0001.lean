module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassSplit
section
noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

private theorem isAddFundamentalDomain_of_existsUnique {V : Type} [AddCommGroup V]
    [MeasurableSpace V] (μ : Measure V) (L : AddSubgroup V) (F : Set V) (hF : MeasurableSet F)
    (h : ∀ v, ∃! l : L, (l : V) + v ∈ F) : IsAddFundamentalDomain L F μ :=
  IsAddFundamentalDomain.mk' hF.nullMeasurableSet fun v => h v

private theorem existsUnique_neg_section_add_mem {V : Type} [AddCommGroup V]
    (L Λ : AddSubgroup V) (σ : L ⧸ Λ.addSubgroupOf L → L)
    (hσ : ∀ q, (QuotientAddGroup.mk (σ q) : L ⧸ Λ.addSubgroupOf L) = q)
    (m : V) (hm : m ∈ L) : ∃! q : L ⧸ Λ.addSubgroupOf L, -((σ q : L) : V) + m ∈ Λ := by
  have key : ∀ q : L ⧸ Λ.addSubgroupOf L,
      (-((σ q : L) : V) + m ∈ Λ ↔ q = QuotientAddGroup.mk ⟨m, hm⟩) := by
    intro q
    have e : q = QuotientAddGroup.mk ⟨m, hm⟩ ↔
        (QuotientAddGroup.mk (σ q) : L ⧸ Λ.addSubgroupOf L) = QuotientAddGroup.mk ⟨m, hm⟩ := by
      rw [hσ q]
    rw [e]
    first
    | rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    | rw [QuotientAddGroup.eq', AddSubgroup.mem_addSubgroupOf]
    first
    | exact Iff.rfl
    | simp
  exact ⟨QuotientAddGroup.mk ⟨m, hm⟩, (key _).2 rfl, fun q hq => (key q).1 hq⟩

private theorem existsUnique_mem_iUnion_translate_preimage {V : Type} [AddCommGroup V]
    (L Λ : AddSubgroup V) (hle : Λ ≤ L) (FL : Set V) (hdL : ∀ v, ∃! l : L, (l : V) + v ∈ FL)
    {ι : Type*} (ρ : ι → V) (hρL : ∀ i, ρ i ∈ L) (hρ : ∀ m ∈ L, ∃! i, ρ i + m ∈ Λ) (v : V) :
    ∃! a : Λ, (a : V) + v ∈ ⋃ i, (fun w => ρ i + w) ⁻¹' FL := by
  obtain ⟨l, hl, hlu⟩ := hdL v
  obtain ⟨i, hi, hiu⟩ := hρ (-(l : V)) (L.neg_mem l.2)
  have ha : (l : V) - ρ i ∈ Λ := by
    have e : (l : V) - ρ i = -(ρ i + -(l : V)) := by abel
    rw [e]
    exact Λ.neg_mem hi
  refine ⟨⟨(l : V) - ρ i, ha⟩, ?_, ?_⟩
  · refine Set.mem_iUnion.2 ⟨i, ?_⟩
    show ρ i + (((l : V) - ρ i) + v) ∈ FL
    rw [show ρ i + (((l : V) - ρ i) + v) = (l : V) + v by abel]
    exact hl
  · intro b hb
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hb
    have hj' : ((⟨ρ j + (b : V), L.add_mem (hρL j) (hle b.2)⟩ : L) : V) + v ∈ FL := by
      show ρ j + (b : V) + v ∈ FL
      rw [add_assoc]
      exact hj
    have hy : ρ j + (b : V) = l := congrArg Subtype.val (hlu _ hj')
    have hj2 : ρ j + -(l : V) ∈ Λ := by
      have e : ρ j + -(l : V) = -(b : V) := by rw [← hy]; abel
      rw [e]
      exact Λ.neg_mem b.2
    have hji : j = i := hiu j hj2
    rw [hji] at hy
    apply Subtype.ext
    show (b : V) = (l : V) - ρ i
    rw [← hy]
    abel

private theorem pairwise_disjoint_translate_preimage {V : Type} [AddCommGroup V]
    (L Λ : AddSubgroup V) (FL : Set V) (hdL : ∀ v, ∃! l : L, (l : V) + v ∈ FL)
    {ι : Type*} (ρ : ι → V) (hρL : ∀ i, ρ i ∈ L) (hρ : ∀ m ∈ L, ∃! i, ρ i + m ∈ Λ) :
    Pairwise (Function.onFun Disjoint fun i => (fun w => ρ i + w) ⁻¹' FL) := by
  intro i j hij
  refine Set.disjoint_left.2 fun w hi hj => hij ?_
  have e : (⟨ρ i, hρL i⟩ : L) = ⟨ρ j, hρL j⟩ :=
    (hdL w).unique (show ((⟨ρ i, hρL i⟩ : L) : V) + w ∈ FL from hi)
      (show ((⟨ρ j, hρL j⟩ : L) : V) + w ∈ FL from hj)
  have e' : ρ i = ρ j := congrArg Subtype.val e
  obtain ⟨q, -, hq⟩ := hρ (-ρ i) (L.neg_mem (hρL i))
  have h1 : i = q := hq i (by simp)
  have h2 : j = q := hq j (by show ρ j + -ρ i ∈ Λ; rw [← e']; simp)
  rw [h1, h2]

theorem fund_index {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V)
    [μ.IsAddLeftInvariant] (L Λ : AddSubgroup V) [Countable L] (hle : Λ ≤ L) (k : ℕ)
    (hk : Λ.relIndex L = k) (hk0 : k ≠ 0) (FL FΛ : Set V) (hFL : MeasurableSet FL) (hFΛ : MeasurableSet FΛ)
    (hdL : ∀ v, ∃! l : L, (l : V) + v ∈ FL) (hdΛ : ∀ v, ∃! a : Λ, (a : V) + v ∈ FΛ) :
    μ FΛ = k * μ FL := by
  classical
  have hcard : Nat.card (L ⧸ Λ.addSubgroupOf L) = k := hk
  haveI : Finite (L ⧸ Λ.addSubgroupOf L) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hk0)
  haveI : Fintype (L ⧸ Λ.addSubgroupOf L) := Fintype.ofFinite _
  haveI : Countable Λ := Function.Injective.countable (AddSubgroup.inclusion_injective hle)
  haveI : MeasurableVAdd Λ V := by
    first
    | infer_instance
    | exact ⟨fun c => measurable_const_add (c : V), fun v => (measurable_add_const v).comp measurable_subtype_coe⟩
  haveI : VAddInvariantMeasure Λ V μ := by
    first
    | infer_instance
    | exact ⟨fun c s _ => measure_preimage_add μ (c : V) s⟩
  have hsurj : Function.Surjective (QuotientAddGroup.mk : L → L ⧸ Λ.addSubgroupOf L) :=
    QuotientAddGroup.mk_surjective
  obtain ⟨ρ, hρL, hρ⟩ : ∃ ρ : L ⧸ Λ.addSubgroupOf L → V,
      (∀ q, ρ q ∈ L) ∧ ∀ m ∈ L, ∃! q, ρ q + m ∈ Λ :=
    ⟨fun q => -((Function.surjInv hsurj q : L) : V), fun q => L.neg_mem (Function.surjInv hsurj q).2,
      fun m hm => existsUnique_neg_section_add_mem L Λ (Function.surjInv hsurj)
        (Function.surjInv_eq hsurj) m hm⟩
  have hmeas : ∀ q, MeasurableSet ((fun w => ρ q + w) ⁻¹' FL) := fun q =>
    measurable_const_add (ρ q) hFL
  have hU : IsAddFundamentalDomain Λ (⋃ q, (fun w => ρ q + w) ⁻¹' FL) μ :=
    isAddFundamentalDomain_of_existsUnique μ Λ _ (MeasurableSet.iUnion hmeas)
      (existsUnique_mem_iUnion_translate_preimage L Λ hle FL hdL ρ hρL hρ)
  have hΛ : IsAddFundamentalDomain Λ FΛ μ := isAddFundamentalDomain_of_existsUnique μ Λ FΛ hFΛ hdΛ
  rw [hΛ.measure_eq hU, measure_iUnion (pairwise_disjoint_translate_preimage L Λ FL hdL ρ hρL hρ) hmeas]
  simp only [measure_preimage_add]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    hcard]

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ShearMp
section
noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

private theorem measurePreserving_pi_shear_of_indep {P : Type} [Fintype P]
    {α : P → Type} [∀ p, AddGroup (α p)] [∀ p, MeasurableSpace (α p)] [∀ p, MeasurableAdd₂ (α p)]
    (μ : ∀ p, Measure (α p)) [∀ p, SigmaFinite (μ p)] [∀ p, (μ p).IsAddRightInvariant]
    (S : P → Prop) [DecidablePred S] (d : ∀ p, (∀ q, α q) → α p) (hd : ∀ p, Measurable (d p))
    (hind : ∀ p, S p → ∀ x x' : ∀ q, α q, (∀ q, ¬ S q → x q = x' q) → d p x = d p x') :
    MeasurePreserving (fun g q => if S q then g q + d q g else g q)
      (Measure.pi μ) (Measure.pi μ) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd μ (fun q => ¬ S q)
  set e := MeasurableEquiv.piEquivPiSubtypeProd α (fun q => ¬ S q) with he
  have hfwd : ∀ g : ∀ q, α q, e g = (fun i : {q // ¬ S q} => g i.1, fun i : {q // ¬ ¬ S q} => g i.1) :=
    fun _ => rfl
  have hsymm : ∀ (x : ∀ i : {q // ¬ S q}, α i) (y : ∀ i : {q // ¬ ¬ S q}, α i) (q : P),
      e.symm (x, y) q = if h : ¬ S q then x ⟨q, h⟩ else y ⟨q, h⟩ := fun _ _ _ => rfl
  let v : (∀ i : {q // ¬ S q}, α i) → ∀ i : {q // ¬ ¬ S q}, α i :=
    fun x i => d i.1 (e.symm (x, 0))
  have hvdef : ∀ x i, v x i = d i.1 (e.symm (x, 0)) := fun _ _ => rfl
  have hv : Measurable v := by
    refine Measurable.of_eval (fun i => ?_)
    exact (hd i.1).comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  have hgm : Measurable (Function.uncurry fun (x : ∀ i : {q // ¬ S q}, α i)
      (y : ∀ i : {q // ¬ ¬ S q}, α i) => fun i => y i + v x i) := by
    refine Measurable.of_eval (fun i => ?_)
    exact Measurable.add ((measurable_pi_apply i).comp measurable_snd)
      ((measurable_pi_apply i).comp (hv.comp measurable_fst))
  have hgae : ∀ᵐ x ∂(Measure.pi fun i : {q // ¬ S q} => μ i),
      Measure.map (fun y : ∀ i : {q // ¬ ¬ S q}, α i => fun i => y i + v x i)
        (Measure.pi fun i : {q // ¬ ¬ S q} => μ i) = Measure.pi fun i : {q // ¬ ¬ S q} => μ i :=
    ae_of_all _ fun x =>
      (measurePreserving_pi (hf := fun i => measurePreserving_add_right (μ i.1) (v x i))).map_eq
  have h2 := MeasurePreserving.skew_product (MeasurePreserving.id _) hgm hgae
  have h3 := MeasurePreserving.symm _ h1
  have key : (fun g q => if S q then g q + d q g else g q) =
      (⇑e.symm ∘ (fun z : (∀ i : {q // ¬ S q}, α i) × (∀ i : {q // ¬ ¬ S q}, α i) =>
        (id z.1, fun i => z.2 i + v z.1 i))) ∘ ⇑e := by
    funext g q
    by_cases hq : S q
    · have hd' : d q (e.symm ((fun i : {q // ¬ S q} => g i.1), 0)) = d q g :=
        hind q hq _ _ (fun q' hq' => by simp [hsymm, hq'])
      simp [hfwd, hsymm, hq, hvdef, hd']
    · simp [hfwd, hsymm, hq]
  rw [key]
  exact (h3.comp h2).comp h1

theorem shear_mp : ∀ (n : ℕ) (P : Type) [Fintype P] [DecidableEq P], Fintype.card P = n →
    ∀ (α : P → Type) [∀ p, AddGroup (α p)] [∀ p, MeasurableSpace (α p)] [∀ p, MeasurableAdd₂ (α p)]
      (μ : ∀ p, Measure (α p)) [∀ p, SigmaFinite (μ p)] [∀ p, (μ p).IsAddRightInvariant]
      (h : P → ℕ) (c : ∀ p, (∀ q, α q) → α p), (∀ p, Measurable (c p)) →
      (∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → c p x = c p x') →
      MeasurePreserving (fun g p => g p + c p g) (Measure.pi μ) (Measure.pi μ) := by
  intro n P _ _ _ α _ _ _ μ _ _ h c hc hdep
  have hstep : ∀ k : ℕ, MeasurePreserving (fun (g : ∀ q, α q) p => if h p < k then g p + c p g else g p)
      (Measure.pi μ) (Measure.pi μ) := by
    intro k
    induction k with
    | zero =>
      have h0 : (fun (g : ∀ q, α q) p => if h p < 0 then g p + c p g else g p) = id := by
        funext g p
        simp
      rw [h0]
      exact MeasurePreserving.id _
    | succ k ih =>
      have hL := measurePreserving_pi_shear_of_indep μ (fun q => h q = k) c hc
        (fun p hp x x' hx => hdep p x x' (fun q hq => hx q (by omega)))
      have heq : (fun (g : ∀ q, α q) p => if h p < k + 1 then g p + c p g else g p) =
          (fun (g : ∀ q, α q) p => if h p < k then g p + c p g else g p) ∘
            (fun (g : ∀ q, α q) q => if h q = k then g q + c q g else g q) := by
        funext g p
        simp only [Function.comp_apply]
        rcases lt_trichotomy (h p) k with hp | hp | hp
        · have hc' : c p (fun q => if h q = k then g q + c q g else g q) = c p g :=
            hdep p _ _ (fun q hq => by simp [show h q ≠ k by omega])
          simp [hp, show h p < k + 1 by omega, show h p ≠ k by omega, hc']
        · simp [hp]
        · simp [show ¬ h p < k + 1 by omega, show ¬ h p < k by omega, show h p ≠ k by omega]
      rw [heq]
      exact ih.comp hL
  have hfull : (fun (g : ∀ q, α q) p => g p + c p g) =
      (fun (g : ∀ q, α q) p => if h p < Finset.univ.sup h + 1 then g p + c p g else g p) := by
    funext g p
    have hle : h p ≤ Finset.univ.sup h := Finset.le_sup (Finset.mem_univ p)
    simp [show h p < Finset.univ.sup h + 1 by omega]
  rw [hfull]
  exact hstep _

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SmatUnitary
section
noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.UkEmb

variable {n k : ℕ}

def Wm (wf : Fin k → Fin n → ℂ) : Matrix (Fin n) (Fin k) ℂ := Matrix.of fun i a => wf a i

def smat (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ) (G : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  1 + Wm wf * (G - 1) * (Wm wf)ᴴ * J

theorem entry (wf : Fin k → Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin k) :
    ((Wm wf)ᴴ * M * Wm wf) a b = star (wf a) ⬝ᵥ (M *ᵥ wf b) := by
  first
  | (rw [Matrix.mul_assoc]; rfl)
  | (simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Wm, Matrix.of_apply, dotProduct,
        Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
     rw [Finset.sum_comm]
     exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

private theorem conjTranspose_Wm_mulVec_apply (wf : Fin k → Fin n → ℂ) (y : Fin n → ℂ) (a : Fin k) :
    ((Wm wf)ᴴ *ᵥ y) a = star (wf a) ⬝ᵥ y := by
  first
  | rfl
  | simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Wm]

private theorem conjTranspose_mul_J_one_add_mul_eq_one_add (J : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin k) ℂ)
    (D : Matrix (Fin k) (Fin k) ℂ) (hF : Fᴴ * J * F = 1) :
    Fᴴ * (J * (1 + F * D * Fᴴ * J)) * F = 1 + D := by
  have key : ∀ {m : Type} [Fintype m] (X : Matrix (Fin k) m ℂ), Fᴴ * (J * (F * X)) = X := by
    intro m _ X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hF, Matrix.one_mul]
  have key2 : Fᴴ * (J * F) = 1 := by rw [← Matrix.mul_assoc, hF]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, key, key2]

private theorem conjTranspose_one_add_mul_J_mul_eq_J (J : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin k) ℂ)
    (D : Matrix (Fin k) (Fin k) ℂ) (hJh : Jᴴ = J) (hF : Fᴴ * J * F = 1) (hD : D + Dᴴ + Dᴴ * D = 0) :
    (1 + F * D * Fᴴ * J)ᴴ * J * (1 + F * D * Fᴴ * J) = J := by
  have key : ∀ {m : Type} [Fintype m] (X : Matrix (Fin k) m ℂ), Fᴴ * (J * (F * X)) = X := by
    intro m _ X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hF, Matrix.one_mul]
  have h0 : J * (F * ((D + Dᴴ + Dᴴ * D) * (Fᴴ * J))) = 0 := by
    rw [hD]; simp
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc] at h0
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hJh]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, key]
  rw [← sub_eq_zero, ← h0]
  abel

private theorem sub_one_add_conjTranspose_defect_eq_zero_of_unitary (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1) :
    (G - 1) + (G - 1)ᴴ + (G - 1)ᴴ * (G - 1) = 0 := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  have e : (Gᴴ - 1) * (G - 1) = Gᴴ * G - Gᴴ - G + 1 := by
    first
    | noncomm_ring
    | (simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one]; abel)
  rw [e, hG]
  abel

variable (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ)
  (hon : ∀ a b, star (wf a) ⬝ᵥ (J *ᵥ wf b) = if a = b then 1 else 0)

include hon in
theorem ortho : (Wm wf)ᴴ * J * Wm wf = 1 := by
  ext a b
  rw [entry, hon, Matrix.one_apply]

include hon in
theorem smat_unitary (hJh : Jᴴ = J) (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1) :
    (smat J wf G)ᴴ * J * smat J wf G = J := by
  unfold smat
  exact conjTranspose_one_add_mul_J_mul_eq_J J (Wm wf) (G - 1) hJh
    (ortho J wf hon) (sub_one_add_conjTranspose_defect_eq_zero_of_unitary G hG)

include hon in
theorem smat_fix (G : Matrix (Fin k) (Fin k) ℂ) (x : Fin n → ℂ) (hx : ∀ a, star (wf a) ⬝ᵥ (J *ᵥ x) = 0) :
    smat J wf G *ᵥ x = x := by
  have hz : (Wm wf)ᴴ *ᵥ (J *ᵥ x) = 0 := by
    funext a
    rw [conjTranspose_Wm_mulVec_apply, hx a, Pi.zero_apply]
  unfold smat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz,
    Matrix.mulVec_zero, add_zero]

include hon in
theorem smat_mat (G : Matrix (Fin k) (Fin k) ℂ) (a b : Fin k) :
    star (wf a) ⬝ᵥ (J *ᵥ (smat J wf G *ᵥ wf b)) = G a b := by
  have hM : (Wm wf)ᴴ * (J * smat J wf G) * Wm wf = G := by
    unfold smat
    rw [conjTranspose_mul_J_one_add_mul_eq_one_add J (Wm wf) (G - 1) (ortho J wf hon)]
    abel
  rw [Matrix.mulVec_mulVec, ← entry, hM]


theorem smat_inv (hJ2 : J * J = 1) (hJh : Jᴴ = J) (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1)
    (hon : ∀ a b, star (wf a) ⬝ᵥ (J *ᵥ wf b) = if a = b then 1 else 0) :
    (J * (smat J wf G)ᴴ * J) * smat J wf G = 1 := by
  have h := smat_unitary J wf hon hJh G hG
  calc (J * (smat J wf G)ᴴ * J) * smat J wf G
      = J * ((smat J wf G)ᴴ * J * smat J wf G) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, hJ2]

end Formalism.L2.SG.Pf.UkEmb
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabilizerMassQuotient
section
noncomputable section

open scoped ENNReal Classical

namespace Formalism.L2.SG.Pf.StabilizerMassQuotient

variable (Γ : Type*) [Group Γ]

variable {Γ}

theorem card_stab_smul {A : Type*} [MulAction Γ A] (g : Γ) (a : A) :
    Nat.card (MulAction.stabilizer Γ (g • a)) = Nat.card (MulAction.stabilizer Γ a) := by
  refine Nat.card_congr
    { toFun := fun s => ⟨g⁻¹ * (s : Γ) * g, by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.1 s.2,
          inv_smul_smul]⟩
      invFun := fun t => ⟨g * (t : Γ) * g⁻¹, by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul,
          MulAction.mem_stabilizer_iff.1 t.2]⟩
      left_inv := fun s => Subtype.ext (by first | simp [mul_assoc] | group)
      right_inv := fun t => Subtype.ext (by first | simp [mul_assoc] | group) }

theorem card_stab_of_orbitRel {A : Type*} [MulAction Γ A] {a a' : A} (h : MulAction.orbitRel Γ A a' a) :
    Nat.card (MulAction.stabilizer Γ a') = Nat.card (MulAction.stabilizer Γ a) := by
  first
  | (obtain ⟨g, rfl⟩ := h; exact card_stab_smul g a)
  | (obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h);
      exact card_stab_smul g a)

section Fibre

variable {A B : Type*} [MulAction Γ A] [MulAction Γ B] (f : A → B)
  (hf : ∀ (g : Γ) (a : A), f (g • a) = g • f a)


include hf in
@[reducible] def fibAct (b : B) : MulAction (MulAction.stabilizer Γ b) {a : A // f a = b} where
  smul s a := ⟨(s : Γ) • a.1, by rw [hf, a.2]; exact s.2⟩
  one_smul a := Subtype.ext (one_smul Γ a.1)
  mul_smul s t a := Subtype.ext (mul_smul (s : Γ) (t : Γ) a.1)


include hf in
def qmap : Quotient (MulAction.orbitRel Γ A) → Quotient (MulAction.orbitRel Γ B) :=
  Quotient.map' f fun a a' ⟨g, hg⟩ => ⟨g, by
    have hg' : g • a' = a := hg
    show g • f a' = f a
    rw [← hf, hg']⟩

theorem qmap_mk (a : A) : qmap f hf (Quotient.mk _ a) = Quotient.mk (MulAction.orbitRel Γ B) (f a) := rfl


include hf in
def stabEquiv (b : B) (x : {a : A // f a = b}) :
    (letI := fibAct f hf b; MulAction.stabilizer (MulAction.stabilizer Γ b) x) ≃ MulAction.stabilizer Γ x.1 := by
  letI := fibAct f hf b
  exact
    { toFun := fun s => ⟨(s.1 : Γ), by
        have h := s.2
        rw [MulAction.mem_stabilizer_iff] at h ⊢
        exact congrArg Subtype.val h⟩
      invFun := fun g => ⟨⟨g.1, by
        rw [MulAction.mem_stabilizer_iff]
        have h := MulAction.mem_stabilizer_iff.1 g.2
        have h2 := congrArg f h
        rw [hf, x.2] at h2
        exact h2⟩, by
          rw [MulAction.mem_stabilizer_iff]
          apply Subtype.ext
          exact (MulAction.mem_stabilizer_iff.1 g.2)⟩
      left_inv := fun s => rfl
      right_inv := fun g => rfl }


include hf in
def orbEquiv (oB : Quotient (MulAction.orbitRel Γ B)) :
    (letI := fibAct f hf oB.out; Quotient (MulAction.orbitRel (MulAction.stabilizer Γ oB.out) {a : A // f a = oB.out})) ≃
      ↥(qmap f hf ⁻¹' {oB}) := by
  letI := fibAct f hf oB.out
  refine Equiv.ofBijective (Quotient.lift (fun x => ⟨Quotient.mk _ x.1, ?_⟩) ?_) ⟨?_, ?_⟩
  · show Quotient.mk _ (f x.1) = oB
    rw [x.2]; exact Quotient.out_eq oB
  · rintro x y ⟨s, hs⟩
    apply Subtype.ext
    exact Quotient.sound ⟨(s : Γ), congrArg Subtype.val hs⟩
  · intro X Y hXY
    induction X using Quotient.inductionOn with | h x => ?_
    induction Y using Quotient.inductionOn with | h y => ?_
    have h := congrArg Subtype.val hXY
    obtain ⟨g, hg⟩ := Quotient.exact h
    have hg' : g • y.1 = x.1 := hg
    have hgb : g • oB.out = oB.out := by
      have h2 := congrArg f hg'
      rw [hf, y.2, x.2] at h2
      exact h2
    exact Quotient.sound ⟨⟨g, hgb⟩, Subtype.ext hg'⟩
  · rintro ⟨oA, hoA⟩
    have hoA' : qmap f hf oA = oB := hoA
    have h1 : Quotient.mk (MulAction.orbitRel Γ B) (f oA.out) = Quotient.mk _ oB.out := by
      rw [← qmap_mk f hf, Quotient.out_eq, hoA', Quotient.out_eq]
    obtain ⟨g, hg⟩ := Quotient.exact h1
    have hg' : g • oB.out = f oA.out := hg
    refine ⟨Quotient.mk _ ⟨g⁻¹ • oA.out, by rw [hf, ← hg', inv_smul_smul]⟩, ?_⟩
    apply Subtype.ext
    show Quotient.mk _ (g⁻¹ • oA.out) = oA
    exact (Quotient.sound ⟨g⁻¹, rfl⟩ : Quotient.mk (MulAction.orbitRel Γ A) (g⁻¹ • oA.out) =
      Quotient.mk _ oA.out).trans (Quotient.out_eq oA)

end Fibre

section Sub

variable {Y : Type*} [MulAction Γ Y]

end Sub

section Pair

variable {Y : Type*} [MulAction Γ Y]

end Pair

section Local

variable {T : Type*} [MulAction Γ T]

end Local

end Formalism.L2.SG.Pf.StabilizerMassQuotient
end
end

