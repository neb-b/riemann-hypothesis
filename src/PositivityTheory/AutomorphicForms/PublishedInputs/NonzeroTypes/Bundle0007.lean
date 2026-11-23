module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Mathlib

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Iwahori₂
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ} (G : Grp k n)

namespace Iwahori₂

theorem inPow_mono {a b : ℕ} (hab : a ≤ b) {x : k} (hx : InPow b x) : InPow a x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, Ideal.pow_le_pow_right hab hy, rfl⟩

theorem inPow_mul {a b : ℕ} {x y : k} (hx : InPow a x) (hy : InPow b y) : InPow (a + b) (x * y) := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨x' * y', by rw [pow_add]; exact Ideal.mul_mem_mul hx' hy', map_mul _ _ _⟩

theorem inPow_add {a : ℕ} {x y : k} (hx : InPow a x) (hy : InPow a y) : InPow a (x + y) := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨x' + y', add_mem hx' hy', map_add _ _ _⟩

theorem inPow_zero (a : ℕ) : InPow a (0 : k) := ⟨0, zero_mem _, map_zero _⟩

theorem inPow_sum {a : ℕ} {ι : Type} (s : Finset ι) (f : ι → k) (h : ∀ i ∈ s, InPow a (f i)) :
    InPow a (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using inPow_zero (k := k) a
  | cons i s hi ih =>
    rw [Finset.sum_cons]
    exact inPow_add (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

theorem inPow_zero_of_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (i j : Fin n) :
    InPow 0 ((g : Matrix (Fin n) (Fin n) k) i j) := by
  obtain ⟨g', rfl⟩ := hg
  exact ⟨(g' : Matrix (Fin n) (Fin n) 𝒪[k]) i j, by simp, rfl⟩

theorem mem_uRL {R : Type} [CommRing R] (X : GL (Fin n) R) :
    X ∈ unipRadLower R G.e ↔ ∀ i j, (G.bl i < G.bl j → (X : Matrix (Fin n) (Fin n) R) i j = 0) ∧
      (G.bl i = G.bl j → (X : Matrix (Fin n) (Fin n) R) i j = if i = j then 1 else 0) := by
  rw [mem_unipRadLower, mem_parabLower_iff]
  constructor
  · rintro ⟨h1, h2⟩ i j
    obtain ⟨⟨a, i'⟩, rfl⟩ := G.e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := G.e.surjective j
    simp only [Grp.bl, Equiv.symm_apply_apply]
    refine ⟨fun h => h1 a b i' j' h, fun h => ?_⟩
    subst h
    rw [h2 a i' j', Matrix.one_apply]
    simp
  · intro h
    refine ⟨fun a b i' j' hab => (h _ _).1 (by simpa [Grp.bl] using hab), fun a i' j' => ?_⟩
    rw [(h _ _).2 (by simp [Grp.bl]), Matrix.one_apply]
    simp

abbrev Lt (b : Fin G.s) : Type := {j : Fin n // G.bl j < b}

theorem isUnit_det_lt (A : GL (Fin n) 𝒪[k])
    (hA : ∀ a, ∃ u : 𝒪[k]ˣ, G.Δ a (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) A) =
      algebraMap 𝒪[k] k u) (b : Fin G.s) :
    IsUnit ((A : Matrix (Fin n) (Fin n) 𝒪[k]).submatrix (Subtype.val : Lt G b → Fin n) Subtype.val).det := by
  rcases Nat.eq_zero_or_pos (b : ℕ) with hb | hb
  · have : IsEmpty (Lt G b) := ⟨fun j => by
      have := j.2
      rw [Fin.lt_def] at this
      omega⟩
    rw [Matrix.det_isEmpty]
    exact isUnit_one
  · let a : Fin G.s := ⟨b - 1, by omega⟩
    obtain ⟨u, hu⟩ := hA a
    have hiff : ∀ j : Fin n, G.bl j ≤ a ↔ G.bl j < b := fun j => by
      simp only [Fin.le_def, Fin.lt_def, a]
      omega
    let f : {j : Fin n // G.bl j ≤ a} ≃ Lt G b := Equiv.subtypeEquivRight hiff
    rw [← Matrix.det_submatrix_equiv_self f]
    have h2 : algebraMap 𝒪[k] k ((A : Matrix (Fin n) (Fin n) 𝒪[k]).submatrix
        (Subtype.val : {j : Fin n // G.bl j ≤ a} → Fin n) Subtype.val).det = algebraMap 𝒪[k] k u := by
      rw [← hu, Grp.Δ, RingHom.map_det]
      rfl
    have h3 := Subtype.val_injective h2
    convert u.isUnit using 2
    exact h3

variable {G}

def rowv (M : Matrix (Fin n) (Fin n) 𝒪[k]) (i : Fin n) : Lt G (G.bl i) → 𝒪[k] :=
  -(Matrix.vecMul (fun j : Lt G (G.bl i) => M i j.1)
    (M.submatrix (Subtype.val : Lt G (G.bl i) → Fin n) Subtype.val)⁻¹)


variable (G) in
def Wm (M : Matrix (Fin n) (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k] :=
  Matrix.of fun i l => if h : G.bl l < G.bl i then rowv M i ⟨l, h⟩ else (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i l

theorem Wm_upper (M : Matrix (Fin n) (Fin n) 𝒪[k]) (i l : Fin n) (h : G.bl i < G.bl l) : Wm G M i l = 0 := by
  have h1 : ¬ G.bl l < G.bl i := not_lt.2 h.le
  have h2 : i ≠ l := fun e => by subst e; exact lt_irrefl _ h
  simp [Wm, h1, Matrix.one_apply_ne h2]

theorem Wm_diag (M : Matrix (Fin n) (Fin n) 𝒪[k]) (i l : Fin n) (h : G.bl i = G.bl l) :
    Wm G M i l = if i = l then 1 else 0 := by
  have h1 : ¬ G.bl l < G.bl i := by rw [h]; exact lt_irrefl _
  simp [Wm, h1, Matrix.one_apply]

theorem det_Wm (M : Matrix (Fin n) (Fin n) 𝒪[k]) : (Wm G M).det = 1 := by
  have hb : (Wm G M).BlockTriangular (fun i => OrderDual.toDual (G.bl i)) := fun i l h =>
    Wm_upper M i l (OrderDual.toDual_lt_toDual.1 h)
  rw [hb.det_fintype]
  refine Finset.prod_eq_one fun c _ => ?_
  have : (Wm G M).toSquareBlock (fun i => OrderDual.toDual (G.bl i)) c = 1 := by
    refine Matrix.ext fun x y => ?_
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    rw [Wm_diag M x.1 y.1 (by simpa using x.2.trans y.2.symm)]
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

theorem Wm_mul (M : Matrix (Fin n) (Fin n) 𝒪[k]) (i j : Fin n) (hij : G.bl j < G.bl i)
    (hu : IsUnit (M.submatrix (Subtype.val : Lt G (G.bl i) → Fin n) Subtype.val).det) :
    (Wm G M * M) i j = 0 := by
  have hs := Fintype.sum_subtype_add_sum_subtype (fun l => G.bl l < G.bl i) (fun l => Wm G M i l * M l j)
  have h1 : ∑ l : Lt G (G.bl i), Wm G M i l.1 * M l.1 j =
      Matrix.vecMul (rowv M i) (M.submatrix (Subtype.val : Lt G (G.bl i) → Fin n) Subtype.val) (⟨j, hij⟩ : Lt G (G.bl i)) := by
    simp only [Matrix.vecMul, dotProduct, Wm, Matrix.of_apply, Matrix.submatrix_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [dite_eq_left l.2]
  have h2 : ∑ l : {l : Fin n // ¬ G.bl l < G.bl i}, Wm G M i l.1 * M l.1 j = M i j := by
    rw [Finset.sum_eq_single ⟨i, lt_irrefl _⟩]
    · simp [Wm]
    · intro l _ hl
      have : l.1 ≠ i := fun h => hl (Subtype.ext h)
      simp [Wm, l.2, Matrix.one_apply_ne' this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Matrix.mul_apply, ← hs]
  erw [h1, h2]
  rw [rowv, Matrix.neg_vecMul, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  simp

theorem leviProj_mem_KO {s : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = n) (p : parab k (stdBlocks d hd))
    (hp : (p : GL (Fin n) k) ∈ KO k (Fin n)) (a : Fin s) :
    leviProj k (stdBlocks d hd) p a ∈ KO k (Fin (d a)) := by
  rw [GlobalTheory.StepData.mem_KO] at hp ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [leviProj_apply]
    exact hp.1 _ _
  · have hinv : (leviProj k (stdBlocks d hd) p a)⁻¹ = leviProj k (stdBlocks d hd) p⁻¹ a := by
      rw [map_inv, Pi.inv_apply]
    rw [hinv, leviProj_apply]
    exact hp.2 _ _

variable (G)

theorem iwahori_of (hΔ : ∀ g ∈ G.JSet, ∀ a, ∃ u : 𝒪[k]ˣ, G.Δ a g = algebraMap 𝒪[k] k u) :
    ∀ g ∈ G.JSet, ∃ v ∈ G.Nbar, v ∈ G.JSet ∧
      ∃ m : Levi k (fun a : Fin G.s => Fin (G.d a)), m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)) ∧
        ∃ u ∈ G.NO, g = v * leviEmb k G.e m * u := by
  intro g hg
  have hΔg := hΔ g hg
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.1 hg.1
  subst hA
  set φ := Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) with hφ
  set M : Matrix (Fin n) (Fin n) 𝒪[k] := (A : Matrix (Fin n) (Fin n) 𝒪[k]) with hM
  have hunit := isUnit_det_lt G A hΔg
  let W : GL (Fin n) 𝒪[k] := Matrix.nonsingInvUnit (Wm G M) (by rw [det_Wm]; exact isUnit_one)
  have hWval : (W : Matrix (Fin n) (Fin n) 𝒪[k]) = Wm G M := rfl
  have hWL : W ∈ unipRadLower 𝒪[k] G.e :=
    (mem_uRL G W).2 fun i j => ⟨Wm_upper M i j, Wm_diag M i j⟩
  have hP : ∀ i j, G.bl j < G.bl i → ((W * A : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) i j = 0 :=
    fun i j h => by rw [Units.val_mul, hWval]; exact Wm_mul M i j h (hunit _)
  have hentry : ∀ X : GL (Fin n) 𝒪[k], ∀ i j, ((φ X : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      algebraMap 𝒪[k] k ((X : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := fun _ _ _ => rfl
  set p := φ (W * A) with hp
  set v := φ W⁻¹ with hv
  have hpP : p ∈ parab k G.e := mem_parab.2 fun i j h => by rw [hentry, hP i j h, map_zero]
  have hpK : p ∈ KO k (Fin n) := ⟨W * A, rfl⟩
  have hvK : v ∈ KO k (Fin n) := ⟨W⁻¹, rfl⟩
  have hgvp : φ A = v * p := by rw [hv, hp, ← map_mul, inv_mul_cancel_left]
  have hvN : v ∈ G.Nbar := by
    have h := (mem_uRL G W⁻¹).1 (inv_mem hWL)
    intro i j
    refine ⟨fun hij => by rw [hentry, (h i j).1 hij, map_zero], fun hij => ?_⟩
    rw [hentry, (h i j).2 hij]
    split_ifs <;> simp
  have hvJ : v ∈ G.JSet := by
    refine ⟨hvK, fun i j hij => ?_⟩
    have hv' : v = φ A * p⁻¹ := by rw [hgvp, mul_inv_cancel_right]
    rw [hv', Units.val_mul, Matrix.mul_apply]
    refine inPow_sum _ _ fun l _ => ?_
    rcases le_or_gt (G.bl l) (G.bl j) with hl | hl
    · have h1 := hg.2 i l (lt_of_le_of_lt hl hij)
      have h3 := inPow_mul h1 (inPow_zero_of_KO (inv_mem hpK) l j)
      rw [add_zero] at h3
      exact inPow_mono (G.ball _ _ _ _ hl hij le_rfl) h3
    · rw [mem_parab.1 (inv_mem hpP) l j hl, mul_zero]
      exact inPow_zero _
  let pp : parab k G.e := ⟨p, hpP⟩
  have hm : leviProj k G.e pp ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)) :=
    (Subgroup.mem_pi _).2 fun a _ => leviProj_mem_KO G.d G.hd pp hpK a
  obtain ⟨u, hu, hpu⟩ := exists_levi_mul_unip k G.e pp
  have hE := leviEmb_mem_KO G.e hm
  have huK : u ∈ KO k (Fin n) := by
    have : u = (leviEmb k G.e (leviProj k G.e pp))⁻¹ * p := by
      rw [eq_inv_mul_iff_mul_eq]
      exact hpu.symm
    rw [this]
    exact mul_mem (inv_mem hE) hpK
  refine ⟨v, hvN, hvJ, leviProj k G.e pp, hm, u, ⟨hu, huK⟩, ?_⟩
  rw [hgvp, mul_assoc, ← hpu]

end Iwahori₂

theorem step_iwahori : IwahoriDecompositionProp G := by
  intro _ hcc hΔ _ _
  exact Iwahori₂.iwahori_of G (hΔ hcc)

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.JacquetKernel
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.JacquetKernel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ} (G : Grp k n)

theorem mem_NO {g : GL (Fin n) k} : g ∈ G.NO ↔ g ∈ unipRad k G.e ∧ g ∈ KO k (Fin n) := Iff.rfl

theorem zEl_eq_dia (ϖ : kˣ) :
    G.zEl ϖ = GlobalTheory.DepthZeroJac.dia G.e ϖ.ne_zero (fun a => G.s - 1 - (a : ℕ)) := by
  apply Units.ext
  rw [GlobalTheory.DepthZeroJac.dia_val]
  ext i j
  obtain ⟨⟨a, i'⟩, rfl⟩ := G.e.surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := G.e.surjective j
  by_cases hab : a = b
  · subst hab
    rw [zEl, leviEmb_apply_same]
    by_cases hij : i' = j'
    · subst hij
      simp [Matrix.scalar_apply, Matrix.diagonal_pow]
    · have hne : G.e ⟨a, i'⟩ ≠ G.e ⟨a, j'⟩ := fun h => hij (by simpa using h)
      simp [Matrix.scalar_apply, Matrix.diagonal_pow, Matrix.diagonal_apply_ne _ hij, hne]
  · rw [zEl, leviEmb_apply_ne _ _ _ hab, Matrix.diagonal_apply_ne]
    intro h
    exact hab (congrArg Sigma.fst (G.e.injective h))

theorem zEl_pow (ϖ : kˣ) (m : ℕ) :
    G.zEl ϖ ^ m = GlobalTheory.DepthZeroJac.dia G.e ϖ.ne_zero (fun a => m * (G.s - 1 - (a : ℕ))) := by
  induction m with
  | zero =>
    rw [pow_zero]
    simp only [zero_mul]
    exact (GlobalTheory.DepthZeroJac.dia_zero G.e ϖ.ne_zero).symm
  | succ m ih =>
    rw [pow_succ, ih, zEl_eq_dia, ← GlobalTheory.DepthZeroJac.dia_add]
    congr 1
    funext a
    show m * (G.s - 1 - (a : ℕ)) + (G.s - 1 - (a : ℕ)) = (m + 1) * (G.s - 1 - (a : ℕ))
    ring

theorem deep_unif {ϖ : kˣ} (h : IsUnif ϖ) : GlobalTheory.IwahoriInj.Deep 1 (ϖ : k) := by
  obtain ⟨w, hw, hwϖ⟩ := h
  rw [GlobalTheory.IwahoriInj.deep_one_iff, ← hwϖ]
  have hnu : ¬ IsUnit w := hw.not_isUnit
  exact (Valuation.Integer.not_isUnit_iff_valuation_lt_one (v := valuation k) (x := w)).1 hnu

theorem intM_of_deep {g : Matrix (Fin n) (Fin n) k} (h : ∀ i j, GlobalTheory.IwahoriInj.Deep 0 ((g - 1) i j)) :
    GlobalTheory.StepData.IntM g := by
  have e : g = (g - 1) + 1 := by abel
  rw [e]
  exact GlobalTheory.StepData.IntM.add (fun i j => GlobalTheory.DepthZeroJac.mem_int_of_deep (h i j))
    (GlobalTheory.StepData.intM_one (k := k) (n := Fin n))

theorem eventually_conj_deep {c : k} (hc : c ≠ 0) (hc1 : GlobalTheory.IwahoriInj.Deep 1 c) {u : GL (Fin n) k}
    (hu : u ∈ unipRad k G.e) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ i j, GlobalTheory.IwahoriInj.Deep 0
      (((GlobalTheory.DepthZeroJac.dia G.e hc (fun a => m * (G.s - 1 - (a : ℕ))) * u *
        (GlobalTheory.DepthZeroJac.dia G.e hc (fun a => m * (G.s - 1 - (a : ℕ))))⁻¹).val - 1) i j) := by
  have key : ∀ᶠ M : ℕ in Filter.atTop, ∀ i j, GlobalTheory.IwahoriInj.Deep (-(M : ℤ)) ((u.val - 1) i j) := by
    simp only [Filter.eventually_all]
    exact fun i j => GlobalTheory.IwahoriInj.eventually_deep _
  filter_upwards [key] with m hm
  intro i j
  rw [GlobalTheory.DepthZeroJac.conj_sub_apply]
  try dsimp only
  by_cases h : blk G.e i < blk G.e j
  · have h1 : ((blk G.e i : Fin G.s) : ℕ) < (blk G.e j : Fin G.s) := h
    have h2 : ((blk G.e j : Fin G.s) : ℕ) < G.s := (blk G.e j).2
    obtain ⟨t, ht⟩ : ∃ t, m * (G.s - 1 - ((blk G.e i : Fin G.s) : ℕ)) =
        m * (G.s - 1 - ((blk G.e j : Fin G.s) : ℕ)) + m + t := by
      refine Nat.exists_eq_add_of_le ?_
      calc m * (G.s - 1 - ((blk G.e j : Fin G.s) : ℕ)) + m
          = m * (G.s - 1 - ((blk G.e j : Fin G.s) : ℕ) + 1) := by ring
        _ ≤ m * (G.s - 1 - ((blk G.e i : Fin G.s) : ℕ)) := Nat.mul_le_mul_left _ (by omega)
    have e1 : ∀ (A : ℕ) (x : k), c ^ (A + m + t) * x * (c ^ A)⁻¹ = c ^ m * c ^ t * x := by
      intro A x
      have hA : c ^ A ≠ 0 := pow_ne_zero _ hc
      rw [pow_add, pow_add]
      calc c ^ A * c ^ m * c ^ t * x * (c ^ A)⁻¹ = (c ^ A * (c ^ A)⁻¹) * (c ^ m * c ^ t * x) := by ring
        _ = c ^ m * c ^ t * x := by rw [mul_inv_cancel₀ hA, one_mul]
    rw [ht, e1]
    have d1 : GlobalTheory.IwahoriInj.Deep ((m : ℤ) * 1) (c ^ m) := GlobalTheory.DepthZeroJac.deep_pow hc1 m
    have d2 : GlobalTheory.IwahoriInj.Deep ((t : ℤ) * 1) (c ^ t) := GlobalTheory.DepthZeroJac.deep_pow hc1 t
    exact ((d1.mul d2).mul (hm i j)).mono (by omega)
  · rw [GlobalTheory.DepthZeroJac.sub_one_of_mem_unipRad hu h, mul_zero, zero_mul]
    exact GlobalTheory.IwahoriInj.deep_zero 0

theorem mem_NO_of_deep {D u : GL (Fin n) k} (hun : D * u * D⁻¹ ∈ unipRad k G.e)
    (h1 : ∀ i j, GlobalTheory.IwahoriInj.Deep 0 (((D * u * D⁻¹).val - 1) i j))
    (h2 : ∀ i j, GlobalTheory.IwahoriInj.Deep 0 (((D * u⁻¹ * D⁻¹).val - 1) i j)) : D * u * D⁻¹ ∈ G.NO := by
  refine (mem_NO G).2 ⟨hun, ?_⟩
  rw [GlobalTheory.StepData.mem_KO]
  have hinv : (D * u * D⁻¹)⁻¹ = D * u⁻¹ * D⁻¹ := by group
  exact ⟨intM_of_deep h1, by rw [hinv]; exact intM_of_deep h2⟩

theorem eventually_conj_mem_NO {ϖ : kˣ} (hϖ : IsUnif ϖ) {u : GL (Fin n) k} (hu : u ∈ unipRad k G.e) :
    ∀ᶠ m : ℕ in Filter.atTop, G.zEl ϖ ^ m * u * (G.zEl ϖ ^ m)⁻¹ ∈ G.NO := by
  have hc1 := deep_unif hϖ
  filter_upwards [eventually_conj_deep G ϖ.ne_zero hc1 hu,
    eventually_conj_deep G ϖ.ne_zero hc1 (inv_mem hu)] with m h1 h2
  rw [zEl_pow]
  refine mem_NO_of_deep G ?_ h1 h2
  refine GlobalTheory.DepthZeroJac.mem_unipRad_of fun i j h => ?_
  rw [GlobalTheory.DepthZeroJac.conj_sub_apply, GlobalTheory.DepthZeroJac.sub_one_of_mem_unipRad hu h, mul_zero, zero_mul]

theorem conj_inv_mem_unipRad (ϖ : kˣ) (m : ℕ) {u : GL (Fin n) k} (hu : u ∈ unipRad k G.e) :
    (G.zEl ϖ ^ m)⁻¹ * u * G.zEl ϖ ^ m ∈ unipRad k G.e := by
  rw [zEl_pow]
  refine GlobalTheory.DepthZeroJac.mem_unipRad_of fun i j h => ?_
  rw [GlobalTheory.DepthZeroJac.conj'_sub_apply, GlobalTheory.DepthZeroJac.sub_one_of_mem_unipRad hu h, mul_zero, zero_mul]

theorem eventually_mem_twKer_NO {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) {ϖ : kˣ} (hϖ : IsUnif ϖ) {x : V}
    (hx : x ∈ twKer π (unipRad k G.e) 1) :
    ∀ᶠ m : ℕ in Filter.atTop, π (G.zEl ϖ ^ m) x ∈ twKer π G.NO 1 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, w, rfl⟩ := hy
    filter_upwards [eventually_conj_mem_NO G hϖ u.2] with m hm
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    have e : π (G.zEl ϖ ^ m) (π (u : GL (Fin n) k) w) =
        π (G.zEl ϖ ^ m * (u : GL (Fin n) k) * (G.zEl ϖ ^ m)⁻¹) (π (G.zEl ϖ ^ m) w) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [e]
    exact Submodule.subset_span ⟨⟨_, hm⟩, π (G.zEl ϖ ^ m) w, by simp⟩
  | zero => simp
  | add y z _ _ hy hz =>
    filter_upwards [hy, hz] with m h1 h2
    rw [map_add (f := _)]
    exact add_mem h1 h2
  | smul a y _ hy =>
    filter_upwards [hy] with m h1
    rw [map_smul]
    exact Submodule.smul_mem _ a h1

theorem isClosed_zero : IsClosed ({0} : Set k) := isClosed_singleton

theorem isClosed_unipRad : IsClosed (unipRad k G.e : Set (GL (Fin n) k)) := by
  have e : (unipRad k G.e : Set (GL (Fin n) k)) =
      ⋂ i, ⋂ j, {g : GL (Fin n) k | ¬ blk G.e i < blk G.e j → (g.val - 1) i j = 0} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun hg i j h => GlobalTheory.DepthZeroJac.sub_one_of_mem_unipRad hg h,
      fun h => GlobalTheory.DepthZeroJac.mem_unipRad_of fun i j hij => h i j hij⟩
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases h : blk G.e i < blk G.e j
  · simp only [h, not_true_eq_false, false_implies, Set.ofPred_true]
    exact isClosed_univ
  · simp only [h, not_false_eq_true, true_implies]
    have hcont : Continuous fun g : GL (Fin n) k => (g.val - 1) i j := by
      have := Units.continuous_val (M := Matrix (Fin n) (Fin n) k)
      fun_prop
    exact isClosed_zero.preimage hcont

theorem isOpen_KO : IsOpen (KO k (Fin n) : Set (GL (Fin n) k)) :=
  Subgroup.isOpen_mono GlobalTheory.StepData.KOne_le_KO GlobalTheory.StepData.isOpen_KOne

theorem isCompact_NO : IsCompact (G.NO : Set (GL (Fin n) k)) := by
  have hKO : IsCompact (KO k (Fin n) : Set (GL (Fin n) k)) := GlobalTheory.SplitFlip.isCompact_KO
  refine hKO.of_isClosed_subset ?_ (fun g hg => ((mem_NO G).1 hg).2)
  show IsClosed ((unipRad k G.e : Set (GL (Fin n) k)) ∩ (KO k (Fin n) : Set (GL (Fin n) k)))
  exact (isClosed_unipRad G).inter (Subgroup.isClosed_of_isOpen _ isOpen_KO)

theorem isOpen_zN (ϖ : kˣ) (m : ℕ) : IsOpen ((G.zN ϖ m : Subgroup ↥G.NO) : Set ↥G.NO) := by
  let f : ↥G.NO →* GL (Fin n) k := (MulAut.conj (G.zEl ϖ ^ m)⁻¹).toMonoidHom.comp G.NO.subtype
  let S : Subgroup ↥G.NO := (KO k (Fin n)).comap f
  have hf : Continuous f := by
    show Continuous fun u : ↥G.NO => (G.zEl ϖ ^ m)⁻¹ * (u : GL (Fin n) k) * (G.zEl ϖ ^ m)⁻¹⁻¹
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hS : IsOpen (S : Set ↥G.NO) := isOpen_KO.preimage hf
  refine Subgroup.isOpen_mono (H₁ := S) ?_ hS
  intro u hu
  have hu' : (G.zEl ϖ ^ m)⁻¹ * (u : GL (Fin n) k) * (G.zEl ϖ ^ m)⁻¹⁻¹ ∈ KO k (Fin n) := hu
  rw [inv_inv] at hu'
  rw [zN, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  refine ⟨(G.zEl ϖ ^ m)⁻¹ * (u : GL (Fin n) k) * G.zEl ϖ ^ m,
    (mem_NO G).2 ⟨conj_inv_mem_unipRad G ϖ m ((mem_NO G).1 u.2).1, hu'⟩, ?_⟩
  change G.zEl ϖ ^ m * ((G.zEl ϖ ^ m)⁻¹ * (u : GL (Fin n) k) * G.zEl ϖ ^ m) * (G.zEl ϖ ^ m)⁻¹ = u
  group

theorem finite_quot (ϖ : kˣ) (m : ℕ) : Finite (↥G.NO ⧸ G.zN ϖ m) := by
  have : CompactSpace ↥G.NO := isCompact_iff_compactSpace.1 (isCompact_NO G)
  exact (G.zN ϖ m).quotient_finite_of_isOpen (isOpen_zN G ϖ m)

end UpperTheory.TNZ.Grp.JacquetKernel

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ}

theorem step_jacKer (G : Grp k n) : G.JacquetKernelProp := by
  intro _ _ _ _ _ _ _ _ _ hU ϖ hϖ V _ _ π hπ x hx h0
  have h1 : x ∈ twKer π (unipRad k G.e) 1 := (Submodule.Quotient.mk_eq_zero _).1 h0
  obtain ⟨m, hm⟩ := (JacquetKernel.eventually_mem_twKer_NO G π hϖ h1).exists
  refine ⟨m, ?_⟩
  have hc : IsCompact (G.NO : Set (GL (Fin n) k)) := JacquetKernel.isCompact_NO G
  have : Finite (↥G.NO ⧸ G.zN ϖ m) := JacquetKernel.finite_quot G ϖ m
  let : Fintype (↥G.NO ⧸ G.zN ϖ m) := Fintype.ofFinite _
  have hfix : ∀ u ∈ G.zN ϖ m,
      π ((u : ↥G.NO) : GL (Fin n) k) (π (G.zEl ϖ ^ m) x) = π (G.zEl ϖ ^ m) x := by
    intro u hu
    rw [zN, Subgroup.mem_subgroupOf] at hu
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.1 hu
    rw [← hyu]
    change π (G.zEl ϖ ^ m * y * (G.zEl ϖ ^ m)⁻¹) (π (G.zEl ϖ ^ m) x) = π (G.zEl ϖ ^ m) x
    have hyx : π y x = x := by
      rw [hx y (hU.1 y hy).1, (hU.1 y hy).2, one_smul]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hyx]
  have hid := GlobalTheory.LocGL.idem_eq_cosetSum hπ hc (G.zN ϖ m) hfix
  rw [(GlobalTheory.LocGL.idem_eq_zero_iff hπ hc).2 hm] at hid
  have hcard : ((Fintype.card (↥G.NO ⧸ G.zN ϖ m) : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have hsum := (smul_eq_zero.1 hid.symm).resolve_left hcard
  show (∑ᶠ c : ↥G.NO ⧸ G.zN ϖ m, π ((Quotient.out c : ↥G.NO) : GL (Fin n) k) (π (G.zEl ϖ ^ m) x)) = 0
  rw [finsum_eq_sum_of_fintype]
  exact hsum

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SphericalOfUnramified
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

theorem step_sphOfUnr : SphericalOfUnramifiedProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc H d v hv hd
  obtain ⟨⟨n, c⟩, rfl⟩ := H.bij.2 v
  have hn : n = d := by rw [← hd, H.dim]
  subst hn
  exact ⟨c.rep.V, inferInstance, inferInstance, c.rep.ρ, c.rep.smooth, c.rep.irr, (H.sph ⟨n, c⟩).2 hv,
    congrArg rc (IrrGL.of_rep ⟨n, c⟩)⟩

end UpperTheory.TNZ
end
end

