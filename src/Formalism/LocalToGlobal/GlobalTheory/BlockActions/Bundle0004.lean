module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.InJSymRestrict
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassMapEstimateOfPartial
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassInjectiveOfDegree
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

theorem unitary_of_hform {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J δ : Matrix (Fin n) (Fin n) E)
    (h : ∀ x y, hform σ J (δ *ᵥ x) (δ *ᵥ y) = hform σ J x y) : cT σ δ * J * δ = J := by
  ext a b
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  rw [Formalism.L2.GlobalTheoryTheory.Comp.hform_mulVec_rect] at h1
  simpa [hform, Pi.single_apply, apply_ite, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq] using h1

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem isUnit_of_extE (Tf : FormsTiedSym D u Ch chOf) (δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (Γ : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) (hΓ : IsUnit Γ.det)
    (hE : IsExt D Tf.til.z0 (RingHom.id D.host.E) δ Γ) : IsUnit δ.det := by
  obtain ⟨P, hP1, -⟩ := exists_projP Tf
  have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
  have h1 : HMul.hMul Γ (iXm D) = HMul.hMul (iXm D) δ := by have := hE.1; rw [hm] at this; exact this
  have hQ : HMul.hMul (HMul.hMul Γ⁻¹ (iXm D)) δ = iXm D := by
    rw [Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, nonsing_inv_mul _ hΓ, Matrix.one_mul]
  have hl : HMul.hMul (HMul.hMul P (HMul.hMul Γ⁻¹ (iXm D))) δ = 1 := by
    rw [Matrix.mul_assoc, hQ, hP1]
  exact Matrix.isUnit_det_of_left_inverse hl


set_option maxHeartbeats 4000000 in
theorem til_injective (Tf : FormsTiedSym D u Ch chOf)
    (hSD : ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : Module.finrank ℚ D.host.E < (D.mem u).A.T - 1) (v : (D.mem u).A.vT) :
    Function.Injective (D.fm u).til := by
  intro c c' h
  obtain ⟨δ, k, G, hδE, hδi, hkE, hG, hy⟩ := til_eq_level Tf (crdFacts_of Tf) hSD hdeg v c c' h
  have hku := lev_isUnit Tf k G hkE
  have hΓ : IsUnit ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1).det := by
    rw [← Units.val_mul]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  have hδu := isUnit_of_extE Tf δ _ hΓ hδE
  set Δ : GL (Fin (D.R.N D.R.m - 1)) D.host.E := ((Matrix.isUnit_iff_isUnit_det δ).mpr hδu).unit with hΔdef
  have hΔv : (Δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) = δ := IsUnit.unit_spec _
  have hΔ : Δ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramP D) := by
    show cT _ (Δ : Matrix _ _ _) * gramP D * (Δ : Matrix _ _ _) = gramP D
    rw [hΔv]; exact unitary_of_hform _ _ _ hδi
  set K : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := ((Matrix.isUnit_iff_isUnit_det k).mpr hku).unit with hKdef
  have hKv : K.1 = k := IsUnit.unit_spec _
  have hK : K ∈ Tf.clsP.lev.U := lev_mem Tf K G (by rw [hKv]; exact hkE) hG
  have hKU : K ∈ UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((Tf.clsP.lev.U_eq K).1 hK).1
  have hc : (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (sigD D : D.host.E →+* D.host.E) =
      (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    ext e
    simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
  have hrU : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Δ ∈ UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Formalism.UG.P.base_change_mem_holds _ _ _ _ _ _ hc _ Δ hΔ
  apply Tf.clsP.y_bij.1
  show (Quotient.mk'' (Tf.clsP.y c) : Cls Tf.clsP.lev) = Quotient.mk'' (Tf.clsP.y c')
  apply (@DoubleCoset.eq _ _ _ _ _ _).2
  refine ⟨⟨_, hrU⟩, ?_, ⟨K⁻¹, inv_mem hKU⟩, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨Δ, hΔ, rfl⟩)
  · exact Subgroup.mem_subgroupOf.2 (inv_mem hK)
  · apply Subtype.ext
    apply Units.ext
    have hKi : k * (K⁻¹).1 = 1 := by
      rw [← hKv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hbc : ((bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Δ : GL _ _) : Matrix _ _ _) = δ.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
      rw [← hΔv]; rfl
    have e : (Tf.clsP.y c').1.1 = δ.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (Tf.clsP.y c).1.1 * (K⁻¹).1 := by
      rw [← hy, Matrix.mul_assoc, hKi, Matrix.mul_one]
    rw [e, ← hbc]
    rfl

theorem class_injective_of_degree
    (hSD : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i), FormsTiedSym D u Ch chOf →
      Module.finrank ℚ D.host.E < (D.mem u).A.T - 1)
    (hv : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i), FormsTiedSym D u Ch chOf →
      Nonempty (D.mem u).A.vT) :
    ClassMapInjective := fun D u Ch chOf Tf =>
  til_injective Tf (hSD D u Ch chOf Tf) (hdeg D u Ch chOf Tf) (hv D u Ch chOf Tf).some

theorem vT_nonempty (D : D7) (u : D.what₂.Word) : Nonempty (D.mem u).A.vT := by
  rw [← Fintype.card_pos_iff, (D.mem u).A.card_vT]
  simp only [Ranks.f, Ranks.n]
  exact Nat.mul_pos (by decide) D.R.toFrame.ord_pos

theorem classMapInjective_of_finrank_lt
    (hSD : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i), FormsTiedSym D u Ch chOf →
      Module.finrank ℚ D.host.E < (D.mem u).A.T - 1) :
    ClassMapInjective :=
  class_injective_of_degree hSD hdeg (fun D u _ _ _ => vT_nonempty D u)

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfClassesFrames
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField

theorem exists_map_of_ratSpan (D : D7) {n : ℕ} {lam : D.what₂.Tau → DomWeight n}
    {p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hp : p ∈ RatSpan D lam) :
    ∃ F : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL, MvPolynomial.map D.what₂.embLL F = p := by
  have hle : RatSpan D lam ≤ (MvPolynomial.map (σ := D.what₂.Tau × Fin n × Fin n) D.what₂.embLL).range.toAddSubgroup := by
    unfold RatSpan
    refine (AddSubgroup.closure_le _).2 ?_
    rintro q ⟨r, f, -, rfl⟩
    refine RingHom.mem_range.2
      ⟨MvPolynomial.C r * Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), ?_⟩
    have hi : D.what₂.embLL.comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
    congr 1
    unfold Formalism.L2.Forms.ten
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.map_rename, MvPolynomial.map_map, hi]
  obtain ⟨F, hF⟩ := RingHom.mem_range.1 (hle hp)
  exact ⟨F, hF⟩

def FramesAt : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (_ : FormsTiedSym D u Ch chOf)
    (s : D.what₂.LL →+* ℂ),
    (∃ o : Frames (gramC (gramN D D.R.m le_rfl) (embS D s)), o.IsON) ∧ ∃ o : Frames (gramC (gramP D) (embS D s)), o.IsON

def NormClsAt : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
    Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u →
    ∀ (h : (D.fm u).PRat) (s : D.what₂.LL →+* ℂ) (x : Vl D u D.R.m)
      (Pc : (D.mem u).C.cls D.R.m → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL),
      (∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
        ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z)) →
    ∀ (Qc : (D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL),
      (∀ c, Tf.valP.eW ((D.fm u).ptEmb ((D.fm u).PtL h x)) c =
        fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c))) →
    ∀ (o : Frames (gramC (gramN D D.R.m le_rfl) (embS D s))), o.IsON →
    ∀ (o' : Frames (gramC (gramP D) (embS D s))), o'.IsON →
    ∀ c, (∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
        (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (MvPolynomial.map s (Qc c))) (subP o'.1 (MvPolynomial.map s (Qc c)))).re ≤
      ptB D u * ((∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
        (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) (subP o.1 (MvPolynomial.map s (Pc ((D.fm u).til c))))
          (subP o.1 (MvPolynomial.map s (Pc ((D.fm u).til c))))).re)

theorem ptB_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ ptB D u :=
  Finset.prod_nonneg fun _ _ => mul_nonneg (zpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)

theorem wt_re_eq (D : D7) (u : D.what₂.Word) (i : ℕ) (c : (D.mem u).C.cls i) :
    ((D.mem u).C.wt i c).re = ((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℝ)⁻¹ := by
  unfold ColumnChain.wt
  rw [show (((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℂ))⁻¹ = ((((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.ofReal_re]

theorem sum_le_of_inj {α β : Type} [Fintype α] [Fintype β] (f : α → β) (hf : Function.Injective f) (a : α → ℝ) (b : β → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y, 0 ≤ b y) (hab : ∀ x, a x ≤ B * b (f x)) : ∑ x, a x ≤ B * ∑ y, b y := by
  classical
  calc ∑ x, a x ≤ ∑ x, B * b (f x) := Finset.sum_le_sum fun x _ => hab x
    _ = B * ∑ y ∈ Finset.univ.image f, b y := by
        rw [Finset.sum_image (fun x _ y _ h => hf h), Finset.mul_sum]
    _ ≤ B * ∑ y, b y := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun y _ _ => hb y) hB

theorem norm_bound_of_classes_frames (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) (hF : FramesAt) (hC : NormClsAt) : NormBoundAtInfinity := by
  intro D u Ch chOf Tf hL hB h v x
  obtain ⟨s, rfl⟩ : ∃ s, InfinitePlace.mk s = v := ⟨v.embedding, v.mk_embedding⟩

  have hx := ((Tf.val D.R.m le_rfl (Or.inr rfl)).rat ((D.fm u).emb D.R.m x)).1 ⟨x, rfl⟩
  choose P hP hPz using hx.2
  choose Pc hPc using fun c => exists_map_of_ratSpan D (hP c)
  have hrep : ∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
      ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z) := fun c z => by rw [hPc c]; exact hPz c z

  have hy := (Tf.valP.rat ((D.fm u).ptEmb ((D.fm u).PtL h x))).1 ⟨_, rfl⟩
  choose Q hQ hQz using hy.2
  choose Qc hQc using fun c => exists_map_of_ratSpan D (hQ c)
  have hrepP : ∀ c, Tf.valP.eW ((D.fm u).ptEmb ((D.fm u).PtL h x)) c =
      fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c)) := fun c => by rw [hQc c]; exact hQz c
  obtain ⟨⟨o, ho⟩, ⟨o', ho'⟩⟩ := hF D u Ch chOf Tf s
  rw [Tf.normP s _ Qc hrepP o' ho', Tf.norm D.R.m le_rfl (Or.inr rfl) s x Pc hrep o ho]
  refine sum_le_of_inj _ (h1 D u Ch chOf Tf) _ _ _ (ptB_nonneg D u) (fun c => ?_) (fun c => ?_)
  · refine mul_nonneg (mul_nonneg ?_ (Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _))
      (Formalism.L2.Ker.ta_nfAll_nonneg ((D.fm u).lam D.R.m) _)
    rw [wt_re_eq]; positivity
  · have hcard : Nat.card ((D.fm u).stabilizer₂ c) = Nat.card ((D.mem u).C.stab D.R.m ((D.fm u).til c)) :=
      Nat.card_congr (Equiv.ofBijective _ (h2 D u Ch chOf Tf c))
    have hk := hC D u Ch chOf Tf hL hB h s x Pc hrep Qc hrepP o ho o' ho' c
    rw [wt_re_eq, ← hcard]
    have hw : 0 ≤ ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ := by positivity
    calc ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ * (∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
          (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (MvPolynomial.map s (Qc c))) (subP o'.1 (MvPolynomial.map s (Qc c)))).re
        = ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ * ((∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
          (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (MvPolynomial.map s (Qc c))) (subP o'.1 (MvPolynomial.map s (Qc c)))).re) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hk hw
      _ = _ := by ring

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.StabiliserBijectiveOfInjection
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms

theorem bij_of_inj_back {A B : Type} [Finite A] (f : A → B) (hf : Function.Injective f) (g : B → A) (hg : Function.Injective g) :
    Function.Bijective f := by
  haveI : Finite B := Finite.of_injective g hg
  exact hf.bijective_of_nat_card_le (Nat.card_le_card_of_injective g hg)

theorem stabiliser_bijective_of_injection
    (h : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i), FormsTiedSym D u Ch chOf →
      ∀ c, ∃ g : (D.mem u).C.stab D.R.m ((D.fm u).til c) → (D.fm u).stabilizer₂ c, Function.Injective g) :
    StabiliserMapBijective := by
  intro D u Ch chOf Tf c
  obtain ⟨g, hg⟩ := h D u Ch chOf Tf c
  exact bij_of_inj_back _ ((D.fm u).stabMap_inj c) g hg

end Formalism.L2.GlobalTheoryTheory.Br
end
end

