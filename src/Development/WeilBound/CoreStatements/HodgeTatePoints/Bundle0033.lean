module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0031
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ReBase

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RcProj
section
noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

section Gen

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {F : Type} [Field F]
  [Fintype F] [DecidableEq F]
variable {N X : Type} [AddCommGroup N] [Module F N] [AddCommGroup X] [Module F X]

def projL (χ : MulChar F R) : (N → C) →ₗ[R] (N → C) where
  toFun := GlobalTheory.CompanionTheory.Ar.GR.proj χ
  map_add' g h := by
    funext x
    simp only [GlobalTheory.CompanionTheory.Ar.GR.proj, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r g := by
    funext x
    simp only [GlobalTheory.CompanionTheory.Ar.GR.proj, Pi.smul_apply, Algebra.smul_def, RingHom.id_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

lemma projL_apply (χ : MulChar F R) (g : N → C) (x : N) :
    projL χ g x = (Fintype.card Fˣ : C)⁻¹ *
      ∑ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * g ((a : F) • x) := rfl

lemma exists_inv_card {v : Valuation C NNReal} (hv : v.Integers R) (p : ℕ) [Fact p.Prime]
    (hvp : v (p : C) < 1) [CharP F p] :
    ∃ u : R, algebraMap R C u = (Fintype.card Fˣ : C)⁻¹ := by
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hq : v ((Fintype.card F : ℕ) : C) < 1 := by
    rw [hn, Nat.cast_pow, map_pow]
    exact pow_lt_one₀ zero_le hvp n.ne_zero
  have h1 : v (Fintype.card Fˣ : C) = 1 := by
    rw [Fintype.card_units, Nat.cast_sub Fintype.card_pos, Nat.cast_one, Valuation.map_sub_swap]
    exact v.map_one_sub_of_lt hq
  exact hv.exists_of_le_one (by rw [map_inv₀, h1, inv_one])

lemma projL_mem (hu : ∃ u : R, algebraMap R C u = (Fintype.card Fˣ : C)⁻¹) (χ : MulChar F R)
    (S : Submodule R (N → C)) (hS : FStable (F := F) S) {g : N → C} (hg : g ∈ S) : projL χ g ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have : projL χ g = u • ∑ a : Fˣ, χ⁻¹ (a : F) • (fun x => g ((a : F) • x)) := by
    funext x
    rw [projL_apply, Pi.smul_apply, Finset.sum_apply, Algebra.smul_def, hu]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => (Algebra.smul_def _ _).symm)
  rw [this]
  exact S.smul_mem _ (S.sum_mem fun a _ => S.smul_mem _ (hS _ g hg))

omit [Fintype F] [DecidableEq F] in
lemma fstable_sq {M : Submodule R (N → C)} (hM : FStable (F := F) M) :
    FStable (F := F) (sqIdeal (augIdeal M)) :=
  fun a _ hg => sq_pull (LinearMap.lsmul F N a).toAddMonoidHom M M (hM a) hg

omit [Fintype F] [DecidableEq F] in
lemma mul_inv_unit (χ : MulChar F R) (a : Fˣ) : χ (a : F) * χ⁻¹ (a : F) = 1 := by
  rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]

omit [Fintype F] [DecidableEq F] in
lemma eig_le_aug (M : Submodule R (N → C)) (χ : MulChar F R) : eig M χ ≤ augIdeal M := by
  intro g hg
  rw [mem_aug]
  refine ⟨hg.1, ?_⟩
  have := hg.2 0 0
  rwa [zero_smul, MulChar.map_zero, map_zero, zero_mul] at this

lemma projL_eig (hu : ∃ u : R, algebraMap R C u = (Fintype.card Fˣ : C)⁻¹) (χ : MulChar F R)
    {M : Submodule R (N → C)} (hM : FStable (F := F) M) {g : N → C} (hg : g ∈ augIdeal M) :
    projL χ g ∈ eig M χ := by
  rw [mem_aug] at hg
  refine ⟨projL_mem hu χ M hM hg.1, fun a x => ?_⟩
  by_cases ha : a = 0
  · rw [ha, zero_smul, MulChar.map_zero, map_zero, zero_mul, projL_apply]
    simp only [smul_zero, hg.2, mul_zero, Finset.sum_const_zero]
  · obtain ⟨a, rfl⟩ := (isUnit_iff_ne_zero.2 ha)
    rw [projL_apply, projL_apply, mul_left_comm, Finset.mul_sum Finset.univ _ (algebraMap R C _),
      ← Equiv.sum_comp (Equiv.mulRight a) (fun b : Fˣ => algebraMap R C (χ (a : F)) *
        (algebraMap R C (χ⁻¹ (b : F)) * g ((b : F) • x)))]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Equiv.coe_mulRight, Units.val_mul, mul_smul, ← mul_assoc, ← map_mul, map_mul χ⁻¹,
      mul_left_comm, mul_inv_unit, mul_one]

lemma projL_self [CharZero C] (χ : MulChar F R) {M : Submodule R (N → C)} {g : N → C}
    (hg : g ∈ eig M χ) : projL χ g = g := by
  funext x
  have h : ∀ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * g ((a : F) • x) = g x := fun a => by
    rw [hg.2, ← mul_assoc, ← map_mul, mul_comm (χ⁻¹ _), mul_inv_unit, map_one, one_mul]
  rw [projL_apply]
  simp only [h]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_mul]

lemma projL_ne [IsDomain R] {χ χ' : MulChar F R} (hne : χ ≠ χ') {M : Submodule R (N → C)}
    {g : N → C} (hg : g ∈ eig M χ') : projL χ g = 0 := by
  funext x
  have h : ∀ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * g ((a : F) • x) =
      algebraMap R C ((χ⁻¹ * χ') (a : F)) * g x := fun a => by
    rw [hg.2, ← mul_assoc, ← map_mul, MulChar.mul_apply]
  have h0 : ∑ a : Fˣ, (χ⁻¹ * χ') (a : F) = 0 := by
    refine sum_hom_units_eq_zero ((χ⁻¹ * χ').toMonoidHom.comp (Units.coeHom F)) fun h1 => hne ?_
    rw [← inv_mul_eq_one]
    refine MulChar.ext fun a => ?_
    rw [MulChar.one_apply_coe]
    exact DFunLike.congr_fun h1 a
  rw [projL_apply]
  simp only [h]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.sum_mul, ← map_sum, h0, map_zero, zero_mul, mul_zero, Pi.zero_apply]

lemma sum_projL [CharZero C] [IsDomain R] (σ : MulChar F R)
    (hσ : ∀ a : Fˣ, σ (a : F) = 1 → a = 1) (g : N → C) :
    ∑ i : Fin (Fintype.card Fˣ), projL (σ ^ ((i : ℕ) + 1)) g = g := by
  funext x
  have h : ∀ a : Fˣ, ∑ i : Fin (Fintype.card Fˣ), (σ ^ ((i : ℕ) + 1))⁻¹ (a : F) =
      if a = 1 then (Fintype.card Fˣ : R) else 0 := by
    intro a
    split_ifs with ha
    · simp [ha]
    · have hp : ∀ i : ℕ, (σ ^ (i + 1))⁻¹ (a : F) = σ⁻¹ (a : F) ^ i * σ⁻¹ (a : F) := fun i => by
        rw [← inv_pow, MulChar.pow_apply_coe, pow_succ]
      simp only [hp]
      rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun i => σ⁻¹ (a : F) ^ i)]
      have h1 := geom_sum_mul (σ⁻¹ (a : F)) (Fintype.card Fˣ)
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one,
        sub_self] at h1
      have h2 : σ⁻¹ (a : F) - 1 ≠ 0 := fun h => ha (hσ a (by
        have := mul_inv_unit σ a
        rwa [sub_eq_zero.1 h, mul_one] at this))
      rw [(mul_eq_zero.1 h1).resolve_right h2, zero_mul]
  rw [Finset.sum_apply]
  simp only [projL_apply]
  rw [← Finset.mul_sum, Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← Finset.sum_mul, ← map_sum, h]
  rw [Finset.sum_eq_single 1 (fun a _ ha => by simp [ha]) (by simp)]
  rw [if_pos rfl, map_natCast, Units.val_one, one_smul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_mul]

lemma projL_funLeft (χ : MulChar F R) (φ : X →ₗ[F] N) (g : N → C) :
    projL χ (LinearMap.funLeft R C φ g) = LinearMap.funLeft R C φ (projL χ g) := by
  funext x
  simp only [projL_apply, LinearMap.funLeft_apply, map_smul]

omit [Fintype F] [DecidableEq F] in
lemma eig_pull (χ : MulChar F R) (φ : X →ₗ[F] N) (M : Submodule R (N → C))
    (M' : Submodule R (X → C)) (h : ∀ g ∈ M, LinearMap.funLeft R C φ g ∈ M') {g : N → C}
    (hg : g ∈ eig M χ) : LinearMap.funLeft R C φ g ∈ eig M' χ :=
  ⟨h g hg.1, fun a x => by simp only [LinearMap.funLeft_apply, map_smul, hg.2]⟩

end Gen

end PositivityTheory.HtPt.Rc
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.ReProd
section
noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix Kronecker

namespace PositivityTheory.HtPt.Re

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def tn {X Y : Type} (M : Submodule R (X → C)) (M' : Submodule R (Y → C)) :
    Submodule R (X × Y → C) :=
  Submodule.span R {F | ∃ g ∈ M, ∃ h ∈ M', F = fun z => g z.1 * h z.2}

theorem mem_tn {X Y : Type} {M : Submodule R (X → C)} {M' : Submodule R (Y → C)} {g : X → C}
    {h : Y → C} (hg : g ∈ M) (hh : h ∈ M') : (fun z : X × Y => g z.1 * h z.2) ∈ tn M M' :=
  Submodule.subset_span ⟨g, hg, h, hh, rfl⟩

def bil {X Y Z : Type} (a : Z → X) (b : Z → Y) : (X → C) →ₗ[R] (Y → C) →ₗ[R] (Z → C) :=
  (LinearMap.mul R (Z → C)).compl₁₂ (LinearMap.funLeft R C a) (LinearMap.funLeft R C b)

theorem bil_span {X Y Z : Type} (a : Z → X) (b : Z → Y) {s : Set (X → C)} {t : Set (Y → C)}
    {P : Submodule R (Z → C)} (H : ∀ g ∈ s, ∀ h ∈ t, (fun z => g (a z) * h (b z)) ∈ P)
    {g : X → C} {h : Y → C} (hg : g ∈ Submodule.span R s) (hh : h ∈ Submodule.span R t) :
    (fun z => g (a z) * h (b z)) ∈ P := by
  have h1 : Submodule.map₂ (bil (R := R) (C := C) a b) (Submodule.span R s) (Submodule.span R t)
      ≤ P := by
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨g, hg, h, hh, rfl⟩
    exact H g hg h hh
  exact h1 (Submodule.apply_mem_map₂ _ hg hh)

theorem tn_cols {X Y : Type} (B : Matrix X X C) (B' : Matrix Y Y C) :
    tn (Submodule.span R (Set.range fun j x => B x j))
      (Submodule.span R (Set.range fun j x => B' x j)) =
    Submodule.span R (Set.range fun j x => (B ⊗ₖ B') x j) := by
  apply le_antisymm
  · rw [tn, Submodule.span_le]
    rintro _ ⟨g, hg, h, hh, rfl⟩
    refine bil_span Prod.fst Prod.snd ?_ hg hh
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨(i, j), rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact mem_tn (g := fun x => B x i) (h := fun x => B' x j) (Submodule.subset_span ⟨i, rfl⟩)
      (Submodule.subset_span ⟨j, rfl⟩)

theorem hasColen_tn {v : Valuation C NNReal} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] {M : Submodule R (X → C)} {M' : Submodule R (Y → C)} {c c' : NNReal}
    (h : HasColen R v M c) (h' : HasColen R v M' c') :
    HasColen R v (tn M M') (c ^ Fintype.card Y * c' ^ Fintype.card X) := by
  obtain ⟨B, rfl, rfl⟩ := h
  obtain ⟨B', rfl, rfl⟩ := h'
  exact ⟨B ⊗ₖ B', tn_cols B B', by rw [Matrix.det_kronecker, map_mul, map_pow, map_pow]⟩

variable {N₁ : Type} [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁]
  {N₂ : Type} [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂]

def hopfProd (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂) :
    HopfOrder (C := C) R (N₁ × N₂) :=
  HopfOrder.ofSpan {F | ∃ g ∈ A₁.carrier, ∃ h ∈ A₂.carrier, F = fun z => g z.1 * h z.2}
    (by
      obtain ⟨B, hB, h⟩ := A₁.lat
      obtain ⟨B', hB', h'⟩ := A₂.lat
      refine ⟨B ⊗ₖ B', ?_, ?_⟩
      · rw [Matrix.det_kronecker]; exact (hB.pow _).mul (hB'.pow _)
      · rw [← tn_cols, ← h, ← h']; rfl)
    (by
      rintro _ ⟨g, hg, h, hh, rfl⟩ z
      obtain ⟨r, hr⟩ := A₁.le_int hg z.1
      obtain ⟨s, hs⟩ := A₂.le_int hh z.2
      exact ⟨r * s, by rw [map_mul, hr, hs]⟩)
    (Submodule.subset_span ⟨1, A₁.one_mem, 1, A₂.one_mem, by funext z; simp⟩)
    (by
      rintro _ ⟨g, hg, h, hh, rfl⟩ _ ⟨g', hg', h', hh', rfl⟩
      refine Submodule.subset_span ⟨_, A₁.mul_mem _ _ hg hg', _, A₂.mul_mem _ _ hh hh', ?_⟩
      funext z
      simp only [Pi.mul_apply]; ring)
    (by
      rintro _ ⟨g, hg, h, hh, rfl⟩
      refine bil_span (fun z : (N₁ × N₂) × (N₁ × N₂) => (z.1.1, z.2.1))
        (fun z : (N₁ × N₂) × (N₁ × N₂) => (z.1.2, z.2.2)) ?_ (A₁.comul g hg) (A₂.comul h hh)
      rintro _ ⟨u, hu, u', hu', rfl⟩ _ ⟨w, hw, w', hw', rfl⟩
      refine Submodule.subset_span ⟨_, mem_tn hu hw, _, mem_tn hu' hw', ?_⟩
      funext z
      ring)
    (by
      rintro _ ⟨g, hg, h, hh, rfl⟩
      exact mem_tn (A₁.antipode g hg) (A₂.antipode h hh))

theorem hopfProd_carrier (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂) :
    (hopfProd A₁ A₂).carrier = tn A₁.carrier A₂.carrier := rfl

theorem tn_inl (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂) :
    (tn A₁.carrier A₂.carrier).map
      (LinearMap.funLeft R C (AddMonoidHom.inl N₁ N₂ : N₁ → N₁ × N₂)) = A₁.carrier := by
  apply le_antisymm
  · rw [tn, Submodule.map_span_le]
    rintro _ ⟨g, hg, h, hh, rfl⟩
    obtain ⟨r, hr⟩ := A₂.le_int hh 0
    convert A₁.carrier.smul_mem r hg using 1
    funext x
    simp [Algebra.smul_def, hr, mul_comm]
  · intro g hg
    exact ⟨_, mem_tn hg A₂.one_mem, by funext x; simp⟩

theorem tn_inr (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂) :
    (tn A₁.carrier A₂.carrier).map
      (LinearMap.funLeft R C (AddMonoidHom.inr N₁ N₂ : N₂ → N₁ × N₂)) = A₂.carrier := by
  apply le_antisymm
  · rw [tn, Submodule.map_span_le]
    rintro _ ⟨g, hg, h, hh, rfl⟩
    obtain ⟨r, hr⟩ := A₁.le_int hg 0
    convert A₂.carrier.smul_mem r hh using 1
    funext x
    simp [Algebra.smul_def, hr]
  · intro g hg
    exact ⟨_, mem_tn A₁.one_mem hg, by funext x; simp⟩

theorem tn_stab₁ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂) :
    ∀ g ∈ tn A₁.carrier A₂.carrier,
      (fun z : N₁ × N₂ => g (z.1, 0)) ∈ tn A₁.carrier A₂.carrier := by
  intro g hg
  have h := Submodule.mem_map_of_mem
    (f := LinearMap.funLeft R C (AddMonoidHom.inl N₁ N₂ : N₁ → N₁ × N₂)) hg
  rw [tn_inl] at h
  convert mem_tn h A₂.one_mem using 1
  funext z
  simp

theorem tn_stab₂ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂) :
    ∀ g ∈ tn A₁.carrier A₂.carrier,
      (fun z : N₁ × N₂ => g (0, z.2)) ∈ tn A₁.carrier A₂.carrier := by
  intro g hg
  have h := Submodule.mem_map_of_mem
    (f := LinearMap.funLeft R C (AddMonoidHom.inr N₁ N₂ : N₂ → N₁ × N₂)) hg
  rw [tn_inr] at h
  convert mem_tn A₁.one_mem h using 1
  funext z
  simp

theorem tn_char {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {N₁ N₂ : Type} [AddCommGroup N₁] [AddCommGroup N₂]
    (e : N₁ × N₂ ≃+ N)
    (hs : ∀ g ∈ AA.carrier, (fun x => g (e ((e.symm x).1, 0))) ∈ AA.carrier) :
    AA.carrier.map (LinearMap.funLeft R C (e : N₁ × N₂ → N)) =
      tn (AA.carrier.map (LinearMap.funLeft R C fun y : N₁ => e (y, 0)))
        (AA.carrier.map (LinearMap.funLeft R C fun y : N₂ => e (0, y))) := by
  have hadd : ∀ z : N₁ × N₂, e (z.1, 0) + e (0, z.2) = e z := fun z => by
    rw [← map_add (f := _)]; simp
  have hs₂ : ∀ g ∈ AA.carrier, (fun x => g (e (0, (e.symm x).2))) ∈ AA.carrier := by
    intro g hg
    have := (stabadd C R N N AA AA (AddMonoidHom.id N)
      (e.toAddMonoidHom.comp ((AddMonoidHom.inl N₁ N₂).comp
        ((AddMonoidHom.fst N₁ N₂).comp e.symm.toAddMonoidHom))) (fun g hg => hg) hs).2 g hg
    convert this using 3 with x
    have h := hadd (e.symm x)
    rw [e.apply_symm_apply] at h
    exact eq_sub_of_add_eq' h
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    have h : (tensorSpan R AA.carrier).map
        (LinearMap.funLeft R C (fun z : N₁ × N₂ => (e (z.1, 0), e (0, z.2)))) ≤
        tn (AA.carrier.map (LinearMap.funLeft R C fun y : N₁ => e (y, 0)))
        (AA.carrier.map (LinearMap.funLeft R C fun y : N₂ => e (0, y))) := by
      rw [tensorSpan, Submodule.map_span_le]
      rintro F ⟨u, hu, w, hw, rfl⟩
      exact mem_tn (Submodule.mem_map_of_mem hu) (Submodule.mem_map_of_mem hw)
    convert h (Submodule.mem_map_of_mem (AA.comul g hg)) using 1
    funext z
    show g (e z) = g (e (z.1, 0) + e (0, z.2))
    rw [hadd]
  · rw [tn, Submodule.span_le]
    rintro _ ⟨_, ⟨u, hu, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨_, AA.mul_mem _ _ (hs u hu) (hs₂ w hw), ?_⟩
    funext z
    simp [LinearMap.funLeft_apply]

end PositivityTheory.HtPt.Re
end
end

