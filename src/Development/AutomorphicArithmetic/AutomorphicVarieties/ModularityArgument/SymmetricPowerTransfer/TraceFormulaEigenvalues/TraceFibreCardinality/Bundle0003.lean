module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.FinsumShift
section
noncomputable section

namespace UpperTheory.V.Z.Sym.Tf

private lemma out_smul_eq {G M : Type} [Group G] (U : Subgroup G) (F : G → M)
    (hF : ∀ g (u : U), F (g * u) = F g) (a : G) (x : G ⧸ U) : F (a • x).out = F (a * x.out) := by
  have h : (a • x : G ⧸ U) = QuotientGroup.mk (a * x.out) := by
    conv_lhs => rw [← QuotientGroup.out_eq' x]
    rfl
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (a * x.out)
  rw [h, hu, hF]

private lemma finsum_shift {G M : Type} [Group G] [AddCommMonoid M] (U : Subgroup G) (F : G → M)
    (hF : ∀ g (u : U), F (g * u) = F g) (a : G) :
    ∑ᶠ x : G ⧸ U, F (a * x.out) = ∑ᶠ x : G ⧸ U, F x.out := by
  rw [← finsum_comp_equiv (MulAction.toPerm a : Equiv.Perm (G ⧸ U)) (f := fun x : G ⧸ U => F x.out)]
  exact finsum_congr fun x => (out_smul_eq U F hF a x).symm

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] {B : Base Γ G V}

private lemma fin_shift (s : B.Tw) {f : G → ℂ} (h : s.IsTest f) (a : G) :
    {z : G ⧸ B.U | f (s.θ (a * z.out)) ≠ 0}.Finite := by
  refine (h.fin.preimage (f := fun z : G ⧸ B.U => a • z) (MulAction.injective a).injOn).subset ?_
  intro z hz
  have := out_smul_eq B.U (fun g => f (s.θ g) ≠ 0) (fun g u => by
    simp only [map_mul, h.right]; simp) a z
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hz ⊢
  rw [this]; exact hz

private lemma conv_eq (s₁ : B.Tw) {f₁ : G → ℂ} (f₂ : G → ℂ) (h₁ : s₁.IsTest f₁) (y : G) :
    s₁.conv f₁ f₂ y = ∑ x ∈ h₁.fin.toFinset, f₁ (s₁.θ x.out) * f₂ (x.out⁻¹ * s₁.θ.symm y) := by
  refine finsum_eq_sum_of_support_subset _ ?_
  intro x hx
  simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
  exact left_ne_zero_of_mul hx

private lemma conv_test (s₁ s₂ : B.Tw) {f₁ f₂ : G → ℂ} (h₁ : s₁.IsTest f₁) (h₂ : s₂.IsTest f₂) :
    (s₁.mul s₂).IsTest (s₁.conv f₁ f₂) := by
  refine ⟨fun u y => ?_, fun u y => ?_, ?_⟩
  · have key := finsum_shift B.U (fun g => f₁ (s₁.θ g) * f₂ (g⁻¹ * s₁.θ.symm (u * y))) (fun g w => by
      have e := h₂.left w⁻¹ (g⁻¹ * s₁.θ.symm (u * y))
      simp only [map_mul s₁.θ, h₁.right, mul_inv_rev, mul_assoc]
      rw [Subgroup.coe_inv] at e
      rw [e, map_inv, inv_inv, mul_left_comm (f₁ _), ← mul_assoc, ← Units.val_mul, inv_mul_cancel]
      simp) (s₁.θ.symm u)
    have hc := conv_eq s₁ f₂ h₁ y
    unfold Base.Tw.conv
    rw [← key]
    unfold Base.Tw.conv at hc
    rw [hc, Finset.mul_sum, finsum_eq_sum_of_support_subset (s := h₁.fin.toFinset)]
    · refine Finset.sum_congr rfl fun x _ => ?_
      simp only [map_mul, MulEquiv.apply_symm_apply, h₁.left, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    · intro x hx
      simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      have := left_ne_zero_of_mul hx
      simp only [map_mul, MulEquiv.apply_symm_apply, h₁.left] at this
      exact right_ne_zero_of_mul this
  · rw [conv_eq s₁ f₂ h₁, conv_eq s₁ f₂ h₁, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : (s₁.mul s₂).θ u = s₁.θ (s₂.θ u) := rfl
    rw [this, map_mul, MulEquiv.symm_apply_apply, ← mul_assoc, h₂.right]
    ring
  · refine (h₁.fin.biUnion fun x _ => fin_shift s₂ h₂ (s₂.θ.symm x.out⁻¹)).subset ?_
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    rw [conv_eq s₁ f₂ h₁] at hz
    obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨x, left_ne_zero_of_mul hne, ?_⟩
    have e : (s₁.mul s₂).θ z.out = s₁.θ (s₂.θ z.out) := rfl
    have := right_ne_zero_of_mul hne
    rw [e, MulEquiv.symm_apply_apply] at this
    rwa [map_mul, MulEquiv.apply_symm_apply]

private lemma opF_comp (s₁ s₂ : B.Tw) {f₁ f₂ : G → ℂ} (h₁ : s₁.IsTest f₁) (h₂ : s₂.IsTest f₂)
    (φ : B.Forms) (g : G) :
    s₁.opF f₁ (s₂.opF f₂ φ.1) g = (s₁.mul s₂).opF (s₁.conv f₁ f₂) φ.1 g := by
  have eθ : ∀ z, s₁.θ.symm ((s₁.mul s₂).θ z) = s₂.θ z := fun z => s₁.θ.symm_apply_apply _
  have eθ' : (s₁.mul s₂).θ.symm g = s₂.θ.symm (s₁.θ.symm g) := rfl
  have eΘ : ∀ v, (s₁.mul s₂).Θ v = s₁.Θ (s₂.Θ v) := fun _ => rfl
  have inner : ∀ x : G, s₂.opF f₂ φ.1 (s₁.θ.symm g * x) =
      ∑ᶠ z : G ⧸ B.U, f₂ (x⁻¹ * s₂.θ z.out) • s₂.Θ (φ.1 (s₂.θ.symm (s₁.θ.symm g) * z.out)) := by
    intro x
    have key := finsum_shift B.U
      (fun z => f₂ (x⁻¹ * s₂.θ z) • s₂.Θ (φ.1 (s₂.θ.symm (s₁.θ.symm g) * z))) (fun z w => by
        rw [map_mul, ← mul_assoc, ← mul_assoc, h₂.right, φ.2.2, map_smul, smul_smul]
        congr 1
        rw [mul_right_comm, ← Units.val_mul, inv_mul_cancel]
        simp) (s₂.θ.symm x)
    rw [← key]
    unfold Base.Tw.opF
    refine finsum_congr fun z => ?_
    simp only [map_mul, MulEquiv.apply_symm_apply, mul_assoc, inv_mul_cancel_left]
  have hfin : ∀ x : G, {z : G ⧸ B.U | f₂ (x⁻¹ * s₂.θ z.out) ≠ 0}.Finite := fun x => by
    simpa only [map_mul, MulEquiv.apply_symm_apply] using fin_shift s₂ h₂ (s₂.θ.symm x⁻¹)
  conv_rhs => unfold Base.Tw.opF
  simp only [conv_eq s₁ f₂ h₁, eθ, eθ', eΘ, Finset.sum_smul]
  rw [finsum_sum_comm]
  · conv_lhs => unfold Base.Tw.opF
    rw [finsum_eq_sum_of_support_subset (s := h₁.fin.toFinset)]
    · refine Finset.sum_congr rfl fun x _ => ?_
      have := inner x.out
      unfold Base.Tw.opF at this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, finsum_eq_sum_of_support_subset (s := (hfin x.out).toFinset),
        finsum_eq_sum_of_support_subset (s := (hfin x.out).toFinset), map_sum, Finset.smul_sum]
      · refine Finset.sum_congr rfl fun z _ => ?_
        rw [map_smul, smul_smul]
      · intro z hz
        simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
        exact right_ne_zero_of_mul (left_ne_zero_of_smul hz)
      · intro z hz
        simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
        exact left_ne_zero_of_smul hz
    · intro x hx
      simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      exact left_ne_zero_of_smul hx
  · intro x _
    refine (hfin x.out).subset fun z hz => ?_
    exact right_ne_zero_of_mul (left_ne_zero_of_smul hz)

end UpperTheory.V.Z.Sym.Tf

theorem UpperTheory.V.Z.Sym.Tf.rMul :
    UpperTheory.V.Z.Sym.Tf.RMul := by
  intro Γ G V _ _ _ _ B s₁ s₂ f₁ f₂ h₁ h₂
  have ht := UpperTheory.V.Z.Sym.Tf.conv_test s₁ s₂ h₁ h₂
  refine ⟨ht, LinearMap.ext fun φ => Subtype.ext ?_⟩
  rw [Module.End.mul_apply, UpperTheory.V.Z.Sym.Tf.rSpec _ _ _ B s₁ f₁ h₁, UpperTheory.V.Z.Sym.Tf.rSpec _ _ _ B s₂ f₂ h₂,
    UpperTheory.V.Z.Sym.Tf.rSpec _ _ _ B _ _ ht]
  funext g
  exact UpperTheory.V.Z.Sym.Tf.opF_comp s₁ s₂ h₁ h₂ φ g
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.OrbOne
section
open UpperTheory.V.Z.Sym MulAction in
theorem UpperTheory.V.Z.Sym.Tf.orbOne :
    UpperTheory.V.Z.Sym.Tf.OrbOne := by
  intro T G _ _ ι C θ U f δ hinv hδ hC hcov
  have h := orbReps T G ι C θ U f δ hinv hδ Unit {()} (fun _ => 1)
    (fun i _ j _ _ _ _ _ => rfl)
    (fun y hy => by
      obtain ⟨t, u, hu, e⟩ := hcov y hy
      exact ⟨t, (), Finset.mem_singleton_self _, u, hu, by simpa using e⟩)
  rw [h, Finset.sum_singleton]
  have hr : (Subgroup.comap ι (stabilizer G ((1 : G) : G ⧸ U))).relIndex C = 1 := by
    rw [Subgroup.relIndex_eq_one]
    intro c hc
    rw [Subgroup.mem_comap, mem_stabilizer_iff, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simpa using hC (Subgroup.mem_map_of_mem ι hc)
  rw [hr]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.OrbProd
section
noncomputable section

namespace UpperTheory.V.Z.Sym.Tf

open MulAction

private lemma thin {T G : Type} [Group T] [Group G] (ι : T →* G) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G)
    (h : FinOrb ι θ U f δ) : ∃ R : Finset G, (∀ a ∈ R, ∀ b ∈ R, ∀ t, ∀ u ∈ U, b = ι t * a * u → a = b) ∧
      ∀ y, f (y⁻¹ * δ * θ y) ≠ 0 → ∃ t, ∃ s ∈ R, ∃ u ∈ U, y = ι t * s * u := by
  classical
  obtain ⟨S, hS⟩ := h
  let r : Setoid G :=
    { r := fun a b => ∃ t, ∃ u ∈ U, b = ι t * a * u
      iseqv := ⟨fun a => ⟨1, 1, U.one_mem, by simp⟩,
        fun {a b} ⟨t, u, hu, e⟩ => ⟨t⁻¹, u⁻¹, U.inv_mem hu, by rw [e]; simp [mul_assoc]⟩,
        fun {a b c} ⟨t, u, hu, e⟩ ⟨t', u', hu', e'⟩ =>
          ⟨t' * t, u * u', U.mul_mem hu hu', by rw [e', e]; simp [mul_assoc]⟩⟩ }
  refine ⟨(S.image (fun s => Quotient.mk r s)).image Quotient.out, ?_, ?_⟩
  · intro a ha b hb t u hu e
    simp only [Finset.mem_image] at ha hb
    obtain ⟨q, -, rfl⟩ := ha
    obtain ⟨q', -, rfl⟩ := hb
    have hr : r q.out q'.out := ⟨t, u, hu, e⟩
    have := Quotient.sound (s := r) hr
    simp only [Quotient.out_eq] at this
    rw [this]
  · intro y hy
    obtain ⟨t, s, hs, u, hu, rfl⟩ := hS y hy
    obtain ⟨t', u', hu', e⟩ : ∃ t', ∃ u' ∈ U, s = ι t' * (Quotient.mk r s).out * u' :=
      Quotient.mk_out (s := r) s
    refine ⟨t * t', _, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hs), u' * u,
      U.mul_mem hu' hu, ?_⟩
    conv_lhs => rw [e]
    simp [mul_assoc]

private lemma glue {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (P : RPG G Gv K)
    (S : Finset I) (j : ∀ v : S, Gv v) : ∃ g, (∀ v : S, P.p v g = j v) ∧ ∀ v ∉ S, P.p v g = 1 := by
  classical
  obtain ⟨g, hg⟩ := P.surj (fun v => if h : v ∈ S then j ⟨v, h⟩ else 1) (by
    rw [Filter.eventually_cofinite]
    refine S.finite_toSet.subset ?_
    intro v hv
    by_contra hvS
    rw [Finset.mem_coe] at hvS
    exact hv (by simp only [dif_neg hvS]; exact (K v).one_mem))
  refine ⟨g, fun v => ?_, fun v hv => ?_⟩
  · rw [hg, dif_pos v.2]
  · rw [hg, dif_neg hv]

private lemma mem_box {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (P : RPG G Gv K)
    (U : ∀ v, Subgroup (Gv v)) (g : G) : g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := by
  simp [RPG.box, Subgroup.mem_iInf]

private lemma index_pi' {J : Type} [Fintype J] {G : J → Type} [∀ j, Group (G j)] (H : ∀ j, Subgroup (G j)) :
    (Subgroup.pi Set.univ H).index = ∏ j, (H j).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y => ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

private lemma relIndex_box {I T : Type} [Group T] {Tv : I → Type} [∀ v, Group (Tv v)] {C₀ : ∀ v, Subgroup (Tv v)}
    (Q : RPG T Tv C₀) (A C : ∀ v, Subgroup (Tv v)) (S : Finset I) (h : ∀ v ∉ S, C v ≤ A v) :
    (Q.box A).relIndex (Q.box C) = ∏ v : S, (A v).relIndex (C v) := by
  classical
  let φ : Q.box C →* ((v : S) → C v) := Pi.monoidHom fun v =>
    ((Q.p v).comp (Q.box C).subtype).codRestrict (C v) (fun x => (mem_box Q C x).1 x.2 v)
  have hφ : Function.Surjective φ := by
    intro j
    obtain ⟨g, hg1, hg2⟩ := glue Q S (fun v => (j v : Tv v))
    have hg : g ∈ Q.box C := by
      rw [mem_box]
      intro v
      by_cases hv : v ∈ S
      · rw [hg1 ⟨v, hv⟩]
        exact (j ⟨v, hv⟩).2
      · rw [hg2 v hv]
        exact (C v).one_mem
    refine ⟨⟨g, hg⟩, ?_⟩
    funext v
    apply Subtype.ext
    exact hg1 v
  have hcomap : (Q.box A).subgroupOf (Q.box C) =
      (Subgroup.pi Set.univ fun v : S => (A v).subgroupOf (C v)).comap φ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ,
      true_implies]
    rw [mem_box]
    constructor
    · intro hx v
      exact hx v
    · intro hx v
      by_cases hv : v ∈ S
      · exact hx ⟨v, hv⟩
      · exact h v hv ((mem_box Q C x).1 x.2 v)
  unfold Subgroup.relIndex
  rw [hcomap]
  exact (Subgroup.index_comap_of_surjective _ hφ).trans (index_pi' _)

private lemma mem_stab {G : Type} [Group G] (U : Subgroup G) (x g : G) :
    g ∈ stabilizer G (x : G ⧸ U) ↔ x⁻¹ * g * x ∈ U := by
  rw [mem_stabilizer_iff, MulAction.Quotient.smul_mk, QuotientGroup.eq, ← U.inv_mem_iff]
  simp [mul_assoc]

set_option maxHeartbeats 800000 in
theorem orbProd : OrbProd := by
  intro I G T _ _ Gv Tv _ _ K U C₀ C P Q ι ιv θ θv f fv δ hι hθ hf hinv hδ S hS hout
  classical
  have hR : ∀ v : S, ∃ R : Finset (Gv v),
      (∀ a ∈ R, ∀ b ∈ R, ∀ t, ∀ u ∈ U v, b = ιv v t * a * u → a = b) ∧
      ∀ y, fv v (y⁻¹ * P.p v δ * θv v y) ≠ 0 → ∃ t, ∃ s ∈ R, ∃ u ∈ U v, y = ιv v t * s * u :=
    fun v => thin (ιv v) (θv v) (U v) (fv v) (P.p v δ) (hS v v.2)
  choose R hRd hRc using hR
  choose x hx1 hx2 using fun c : ((v : S) → Gv v) => glue P S c
  have hsupp : ∀ y, (Function.mulSupport fun v => fv v (P.p v (y⁻¹ * δ * θ y))).Finite := by
    intro y
    have hae := P.ae y
    rw [Filter.eventually_cofinite] at hae
    refine (hae.union S.finite_toSet).subset ?_
    intro v hv
    by_contra hvn
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, not_or, not_not] at hvn
    rw [Function.mem_mulSupport] at hv
    apply hv
    obtain ⟨hK, -, -, h1, -⟩ := hout v hvn.2
    simp only [map_mul, map_inv, hθ]
    rw [hinv v _ (hK hvn.1), h1]
  have hcov : ∀ y, f (y⁻¹ * δ * θ y) ≠ 0 →
      ∃ t, ∃ c ∈ Fintype.piFinset R, ∃ u ∈ P.box U, y = ι t * x c * u := by
    intro y hy
    have hloc : ∀ v, fv v ((P.p v y)⁻¹ * P.p v δ * θv v (P.p v y)) ≠ 0 := by
      intro v h0
      apply hy
      rw [hf]
      refine finprod_eq_zero _ v ?_ (hsupp y)
      simpa only [map_mul, map_inv, hθ] using h0
    have hA : ∀ v : S, ∃ tv, ∃ s ∈ R v, ∃ uv ∈ U v, P.p v y = ιv v tv * s * uv :=
      fun v => hRc v (P.p v y) (hloc v)
    choose tS c hc uS huS heS using hA
    have hB : ∀ v, v ∉ S → ∃ tv, ∃ uv ∈ U v, P.p v y = ιv v tv * uv :=
      fun v hv => (hout v hv).2.2.2.2 _ (hloc v)
    let tv : (v : I) → Tv v := fun v =>
      if hv : v ∈ S then tS ⟨v, hv⟩ else if P.p v y ∈ K v then 1 else (hB v hv).choose
    obtain ⟨t, ht⟩ := Q.surj tv (by
      have hae := P.ae y
      rw [Filter.eventually_cofinite] at hae ⊢
      refine (hae.union S.finite_toSet).subset ?_
      intro v hv
      by_contra hvn
      simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, not_or, not_not] at hvn
      apply hv
      simp only [tv, dif_neg hvn.2, if_pos hvn.1]
      exact (C₀ v).one_mem)
    refine ⟨t, c, Fintype.mem_piFinset.2 hc, (ι t * x c)⁻¹ * y, ?_, by group⟩
    rw [mem_box]
    intro v
    rw [map_mul, map_inv, map_mul, hι, ht]
    by_cases hv : v ∈ S
    · have e1 : P.p v (x c) = c ⟨v, hv⟩ := hx1 c ⟨v, hv⟩
      have e2 : P.p v y = ιv v (tS ⟨v, hv⟩) * c ⟨v, hv⟩ * uS ⟨v, hv⟩ := heS ⟨v, hv⟩
      simp only [tv, dif_pos hv, e1, e2]
      simpa [mul_assoc] using huS ⟨v, hv⟩
    · rw [hx2 c v hv]
      by_cases hK : P.p v y ∈ K v
      · simp only [tv, dif_neg hv, if_pos hK, map_one, mul_one, inv_one, one_mul]
        exact (hout v hv).1 hK
      · simp only [tv, dif_neg hv, if_neg hK, mul_one]
        obtain ⟨uv, huv, euv⟩ := (hB v hv).choose_spec
        have e3 : (ιv v (hB v hv).choose)⁻¹ * P.p v y = uv := by
          rw [inv_mul_eq_iff_eq_mul]
          exact euv
        rw [e3]
        exact huv
  have hdist : ∀ c ∈ Fintype.piFinset R, ∀ c' ∈ Fintype.piFinset R, ∀ t, ∀ u ∈ P.box U,
      x c' = ι t * x c * u → c = c' := by
    intro c hc c' hc' t u hu e
    funext v
    have e' := congrArg (P.p v) e
    rw [map_mul, map_mul, hι, hx1, hx1] at e'
    exact hRd v (c v) (Fintype.mem_piFinset.1 hc v) (c' v) (Fintype.mem_piFinset.1 hc' v)
      (Q.p v t) (P.p v u) ((mem_box P U u).1 hu v) e'
  have hfinv : ∀ u ∈ P.box U, ∀ g, f (u⁻¹ * g * θ u) = f g := by
    intro u hu g
    rw [hf, hf]
    refine finprod_congr (fun v => ?_)
    simp only [map_mul, map_inv, hθ]
    exact hinv v _ ((mem_box P U u).1 hu v) _
  have hδg : ∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ := by
    intro t
    have h1 := P.inj ((ι t)⁻¹ * δ * θ (ι t) * δ⁻¹) (fun v => by
      simp only [map_mul, map_inv, hθ, hι]
      rw [hδ v (Q.p v t)]
      simp)
    exact mul_inv_eq_one.1 h1
  have hglob := orbReps T G ι (Q.box C) θ (P.box U) f δ hfinv hδg _ (Fintype.piFinset R) x
    hdist hcov
  refine ⟨?_, ?_⟩
  · unfold FinOrb
    refine ⟨(Fintype.piFinset R).image x, fun y hy => ?_⟩
    obtain ⟨t, c, hc, u, hu, e⟩ := hcov y hy
    exact ⟨t, x c, Finset.mem_image_of_mem _ hc, u, hu, e⟩
  · rw [hglob]
    have hloc : ∏ v ∈ S, orb (ιv v) (C v) (θv v) (U v) (fv v) (P.p v δ) =
        ∏ v : S, ∑ s ∈ R v, ((Subgroup.comap (ιv v)
          (stabilizer (Gv v) (s : Gv v ⧸ U v))).relIndex (C v) : ℂ) *
            fv v (s⁻¹ * P.p v δ * θv v s) := by
      rw [← Finset.prod_coe_sort]
      refine Finset.prod_congr rfl (fun v _ => ?_)
      exact orbReps (Tv v) (Gv v) (ιv v) (C v) (θv v) (U v) (fv v) (P.p v δ) (hinv v) (hδ v)
        (Gv v) (R v) id (hRd v) (hRc v)
    rw [hloc, Finset.prod_univ_sum]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [Finset.prod_mul_distrib]
    congr 1
    · have hA : Subgroup.comap ι (stabilizer G ((x c : G) : G ⧸ P.box U)) =
          Q.box (fun v => Subgroup.comap (ιv v)
            (stabilizer (Gv v) ((P.p v (x c) : Gv v) : Gv v ⧸ U v))) := by
        ext t
        rw [Subgroup.mem_comap, mem_stab, mem_box, mem_box]
        refine forall_congr' (fun v => ?_)
        rw [Subgroup.mem_comap, mem_stab, map_mul, map_mul, map_inv, hι]
      have hCA : ∀ v ∉ S, C v ≤ Subgroup.comap (ιv v)
          (stabilizer (Gv v) ((P.p v (x c) : Gv v) : Gv v ⧸ U v)) := by
        intro v hv a ha
        rw [Subgroup.mem_comap, mem_stab, hx2 c v hv]
        simpa using (hout v hv).2.2.1 (Subgroup.mem_map_of_mem _ ha)
      rw [hA, relIndex_box Q _ C S hCA, Nat.cast_prod]
      refine Finset.prod_congr rfl (fun v _ => ?_)
      rw [hx1 c v]
    · rw [hf, finprod_eq_prod_of_mulSupport_subset (s := S) _ ?_, ← Finset.prod_coe_sort]
      · refine Finset.prod_congr rfl (fun v _ => ?_)
        simp only [map_mul, map_inv, hθ, hx1 c v]
      · intro v hv
        rw [Finset.mem_coe]
        by_contra hvS
        rw [Function.mem_mulSupport] at hv
        apply hv
        simp only [map_mul, map_inv, hθ, hx2 c v hvS, inv_one, one_mul, map_one, mul_one]
        exact (hout v hvS).2.2.2.1

end UpperTheory.V.Z.Sym.Tf
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.RLin
section
theorem UpperTheory.V.Z.Sym.Tf.rLin :
    UpperTheory.V.Z.Sym.Tf.RLin := by
  classical
  intro Γ G V _ _ _ _ B s I S c f hf
  have hT : {x : G ⧸ B.U | ∃ i ∈ S, f i (s.θ x.out) ≠ 0}.Finite := by
    refine (Set.Finite.biUnion S.finite_toSet (fun i hi => (hf i hi).fin)).subset ?_
    rintro x ⟨i, hi, hx⟩
    exact Set.mem_biUnion (show i ∈ (S : Set I) from hi) hx
  have htest : s.IsTest (fun y => ∑ i ∈ S, c i * f i y) := by
    refine ⟨fun u y => ?_, fun u y => ?_, hT.subset ?_⟩
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(hf i hi).left]; ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(hf i hi).right]; ring
    · intro x hx
      obtain ⟨i, hi, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      exact ⟨i, hi, right_ne_zero_of_mul h⟩
  refine ⟨htest, ?_⟩
  refine LinearMap.ext fun φ => Subtype.ext ?_
  rw [UpperTheory.V.Z.Sym.Tf.rSpec Γ G V B s _ htest φ, LinearMap.sum_apply, Submodule.coe_sum]
  funext g
  rw [Finset.sum_apply]
  have key : ∀ h : G → ℂ, (∀ x : G ⧸ B.U, h (s.θ x.out) ≠ 0 → ∃ i ∈ S, f i (s.θ x.out) ≠ 0) →
      s.opF h φ.1 g = ∑ x ∈ hT.toFinset, h (s.θ x.out) • s.Θ (φ.1 (s.θ.symm g * x.out)) := by
    intro h hh
    refine finsum_eq_sum_of_support_subset _ fun x hx => ?_
    rw [Set.Finite.coe_toFinset]
    exact hh x (left_ne_zero_of_smul hx)
  rw [key _ (fun x hx => by
    obtain ⟨i, hi, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    exact ⟨i, hi, right_ne_zero_of_mul h⟩)]
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
    UpperTheory.V.Z.Sym.Tf.rSpec Γ G V B s _ (hf i hi) φ, key _ (fun x hx => ⟨i, hi, hx⟩), Finset.smul_sum]
  simp only [mul_smul]
end

