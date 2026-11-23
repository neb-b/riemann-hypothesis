module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.BlockTriangularLevi
section
namespace UpperTheory.Reformulated.B.P6.BlockTriangularLevi

open scoped Sigma DFunLike EquivLike Equiv Matrix CommSemiring CommRing Membership Set Preorder PartialOrder SemilatticeInf Lattice DistribLattice MulZeroClass Units Semiring HMul MulOne MulOneClass Monoid DivInvMonoid Group OfNat One Inv InvOneClass DivInvOneMonoid DivisionMonoid Subgroup Submonoid Subsemigroup Subtype SetLike MulZeroOneClass MonoidHom OneHom Pi PUnit Fin Finset HAdd AddMonoidWithOne AddGroupWithOne Ring DivisionRing Field CommGroup Circle DivisionSemiring Semifield Complex SeminormedRing SeminormedCommRing NormedCommRing NormedField AddChar Zero HSub

noncomputable def GlobalTheory.SmGL.blk :
    {α n : Type} → {m : α → Type} → (a : α) × m a ≃ n → n → α :=
  fun {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (i : n) ↦ Sigma.fst (β := fun (a : α) ↦ m a) (DFunLike.coe (β := fun (x_h1 : n) ↦ (a : α) × m a) e.symm i)

theorem blockIndex_sigma_equiv {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (a : α) (i : m a) :
    GlobalTheory.SmGL.blk (m := m) e (e ⟨a, i⟩) = a := by
  show (e.symm (e ⟨a, i⟩)).1 = a
  rw [Equiv.symm_apply_apply]

theorem blockTriangular_mul_submatrix {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [Fintype n] (e : (a : α) × m a ≃ n) (a : α) (X Y : Matrix n n R)
    (hX : X.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e))
    (hY : Y.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)) :
    (X * Y).submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩)
      = X.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩)
        * Y.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← e.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro l _
    rcases lt_or_gt_of_ne hb with h | h
    · have h' : GlobalTheory.SmGL.blk (m := m) e (e ⟨b, l⟩) < GlobalTheory.SmGL.blk (m := m) e (e ⟨a, i⟩) := by
        rw [blockIndex_sigma_equiv, blockIndex_sigma_equiv]; exact h
      rw [hX h', zero_mul]
    · have h' : GlobalTheory.SmGL.blk (m := m) e (e ⟨a, j⟩) < GlobalTheory.SmGL.blk (m := m) e (e ⟨b, l⟩) := by
        rw [blockIndex_sigma_equiv, blockIndex_sigma_equiv]; exact h
      rw [hY h', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem GlobalTheory.SmGL.parab_obl_1 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : Fintype n] [inst_h4 : DecidableEq n] (e : (a : α) × m a ≃ n) {x y : GL n R}, Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} x → Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} y → Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} (x * y) := by
  intro R _ α n m _ _ _ e x y hx hy
  show ((x * y : GL n R) : Matrix n n R).BlockTriangular _
  rw [Units.val_mul]
  exact Matrix.BlockTriangular.mul hx hy

theorem GlobalTheory.SmGL.parab_obl_2 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : Fintype n] [inst_h4 : DecidableEq n] (e : (a : α) × m a ≃ n), Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} (OfNat.ofNat (nat_lit 1)) := by
  intro R _ α n m _ _ _ e
  show ((1 : GL n R) : Matrix n n R).BlockTriangular _
  rw [Units.val_one]
  exact Matrix.blockTriangular_one

theorem GlobalTheory.SmGL.parab_obl_3 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : Fintype n] [inst_h4 : DecidableEq n] (e : (a : α) × m a ≃ n) {x : GL n R}, Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} x → Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} x⁻¹ := by
  intro R _ α n m _ _ _ e x hx
  show ((x⁻¹ : GL n R) : Matrix n n R).BlockTriangular _
  rw [Matrix.coe_units_inv]
  haveI : Invertible (x : Matrix n n R) := x.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hx

noncomputable def GlobalTheory.SmGL.parab :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : LinearOrder α] → [inst_h3 : Fintype n] → [inst_h4 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
  fun (R : Type) {inst_h0 : CommRing R} {α n : Type} {m : α → Type} {inst_h2 : LinearOrder α} {inst_h3 : Fintype n} {inst_h4 : DecidableEq n} (e : (a : α) × m a ≃ n) ↦ { carrier := {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)}, mul_mem' := @GlobalTheory.SmGL.parab_obl_1 R inst_h0 α n m inst_h2 inst_h3 inst_h4 e, one_mem' := GlobalTheory.SmGL.parab_obl_2 R (m := m) e, inv_mem' := @GlobalTheory.SmGL.parab_obl_3 R inst_h0 α n m inst_h2 inst_h3 inst_h4 e }

@[reducible] noncomputable def GlobalTheory.SmGL.Levi :
    (R : Type) → [inst_h0 : CommRing R] → {α : Type} → (m : α → Type) → [inst_h2 : (a : α) → Fintype (m a)] → [inst_h3 : (a : α) → DecidableEq (m a)] → Type :=
  fun (R : Type) {inst_f0 : CommRing R} {α : Type} (m : α → Type) {inst_f1 : (a : α) → Fintype (m a)} {inst_f2 : (a : α) → DecidableEq (m a)} ↦ (a : α) → GL (m a) R

theorem GlobalTheory.SmGL.diagBlock_obl_1 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : (a : α) → Fintype (m a)] [inst_h4 : (a : α) → DecidableEq (m a)] [inst_h5 : Fintype n] [inst_h6 : DecidableEq n] (e : (a : α) × m a ≃ n) (a : α), Eq (α := Matrix (m a) (m a) R) (Matrix.submatrix (m := n) (n := n) (Units.val (Subtype.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x) (OfNat.ofNat (nat_lit 1)))) (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h7 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h8 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) (OfNat.ofNat (nat_lit 1)) := by
  intro R _ α n m _ _ _ _ _ e a
  show ((1 : GL n R) : Matrix n n R).submatrix _ _ = 1
  rw [Units.val_one]
  exact Matrix.submatrix_one _ (e.injective.comp sigma_mk_injective)

theorem GlobalTheory.SmGL.diagBlock_obl_2 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : Fintype α] [inst_h3 : LinearOrder α] [inst_h4 : (a : α) → Fintype (m a)] [inst_h5 : (a : α) → DecidableEq (m a)] [inst_h6 : Fintype n] [inst_h7 : DecidableEq n] (e : (a : α) × m a ≃ n) (a : α) (x y : ↥(GlobalTheory.SmGL.parab R (m := m) e)), ((x * y).val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h8 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h9 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) = HMul.hMul (α := Matrix (m a) (m a) R) (x.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h10 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h11 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) (y.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h12 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h13 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) := by
  intro R _ α n m _ _ _ _ _ _ e a x y
  have hx : ((x : GL n R) : Matrix n n R).BlockTriangular (GlobalTheory.SmGL.blk (m := m) e) := x.2
  have hy : ((y : GL n R) : Matrix n n R).BlockTriangular (GlobalTheory.SmGL.blk (m := m) e) := y.2
  have key := blockTriangular_mul_submatrix e a _ _ hx hy
  exact key

noncomputable def GlobalTheory.SmGL.diagBlock :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : Fintype α] → [inst_h3 : LinearOrder α] → [inst_h4 : (a : α) → Fintype (m a)] → [inst_h5 : (a : α) → DecidableEq (m a)] → [inst_h6 : Fintype n] → [inst_h7 : DecidableEq n] → (e : (a : α) × m a ≃ n) → (a : α) → ↥(GlobalTheory.SmGL.parab R (m := m) e) →* Matrix (m a) (m a) R :=
  fun (R : Type) {inst_f3 : CommRing R} {α n : Type} {m : α → Type} {inst_f4 : Fintype α} {inst_f5 : LinearOrder α} {inst_f6 : (a : α) → Fintype (m a)} {inst_f7 : (a : α) → DecidableEq (m a)} {inst_f8 : Fintype n} {inst_f9 : DecidableEq n} (e : (a : α) × m a ≃ n) (a : α) ↦ { toFun := fun (p : ↥(GlobalTheory.SmGL.parab R (m := m) e)) ↦ p.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h8 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h9 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i), map_one' := GlobalTheory.SmGL.diagBlock_obl_1 R (m := m) e a, map_mul' := GlobalTheory.SmGL.diagBlock_obl_2 R (m := m) e a }

noncomputable def GlobalTheory.SmGL.leviProj :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : Fintype α] → [inst_h3 : LinearOrder α] → [inst_h4 : (a : α) → Fintype (m a)] → [inst_h5 : (a : α) → DecidableEq (m a)] → [inst_h6 : Fintype n] → [inst_h7 : DecidableEq n] → (e : (a : α) × m a ≃ n) → ↥(GlobalTheory.SmGL.parab R (m := m) e) →* GlobalTheory.SmGL.Levi R m :=
  fun (R : Type) {inst_f10 : CommRing R} {α n : Type} {m : α → Type} {inst_f11 : Fintype α} {inst_f12 : LinearOrder α} {inst_f13 : (a : α) → Fintype (m a)} {inst_f14 : (a : α) → DecidableEq (m a)} {inst_f15 : Fintype n} {inst_f16 : DecidableEq n} (e : (a : α) × m a ≃ n) ↦ MonoidHom.pi (f := fun (a : α) ↦ GL (m a) R) fun (a : α) ↦ MonoidHom.toHomUnits (GlobalTheory.SmGL.diagBlock R (m := m) e a)

noncomputable def GlobalTheory.SmGL.unipRad :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : Fintype α] → [inst_h3 : LinearOrder α] → [inst_h4 : (a : α) → Fintype (m a)] → [inst_h5 : (a : α) → DecidableEq (m a)] → [inst_h6 : Fintype n] → [inst_h7 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
  fun (R : Type) {inst_f17 : CommRing R} {α n : Type} {m : α → Type} {inst_f18 : Fintype α} {inst_f19 : LinearOrder α} {inst_f20 : (a : α) → Fintype (m a)} {inst_f21 : (a : α) → DecidableEq (m a)} {inst_f22 : Fintype n} {inst_f23 : DecidableEq n} (e : (a : α) × m a ≃ n) ↦ Subgroup.map (G := ↥(GlobalTheory.SmGL.parab R (m := m) e)) (Subgroup.subtype (GlobalTheory.SmGL.parab R (m := m) e)) (MonoidHom.ker (GlobalTheory.SmGL.leviProj R (m := m) e))

noncomputable def GlobalTheory.SmGL.points :
    (n : Type) → (_ : n) × Unit ≃ n :=
  fun (n : Type) ↦ Equiv.sigmaUnique n fun (x_h0 : n) ↦ Unit

noncomputable def GlobalTheory.SmGL.unipB :
    (R : Type) → [inst_h0 : CommRing R] → (n : Type) → [inst_h1 : Fintype n] → [inst_h2 : DecidableEq n] → [inst_h3 : LinearOrder n] → Subgroup (GL n R) :=
  fun (R : Type) {inst_f24 : CommRing R} (n : Type) {inst_f25 : Fintype n} {inst_f26 : DecidableEq n} {inst_f27 : LinearOrder n} ↦ GlobalTheory.SmGL.unipRad R (m := fun (a : n) ↦ Unit) (GlobalTheory.SmGL.points n)

noncomputable def GlobalTheory.Whittaker.superDiag :
    {R : Type} → [inst_h0 : CommRing R] → {n : ℕ} → GL (Fin n) R → R :=
  fun {R : Type} {inst_f28 : CommRing R} {n : ℕ} (g : GL (Fin n) R) ↦ ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + OfNat.ofNat (nat_lit 1), g.val i j

noncomputable def DiscreteGroups.sglob.LConv.IsWhitTest :
    {k : Type} → [inst_h0 : Field k] → [inst_h1 : TopologicalSpace k] → {m : ℕ} → AddChar k Circle → (GL (Fin m) k → ℂ) → Prop :=
  fun {k : Type} {inst_f29 : Field k} {inst_f30 : TopologicalSpace k} {m : ℕ} (ψ : AddChar k Circle) (f : GL (Fin m) k → ℂ) ↦ (∀ (u : GL (Fin m) k), Membership.mem (γ := Subgroup (GL (Fin m) k)) (GlobalTheory.SmGL.unipB k (Fin m)) u → ∀ (g : GL (Fin m) k), f (u * g) = Subtype.val (p := fun (x : ℂ) ↦ Membership.mem (γ := Submonoid ℂ) (Submonoid.unitSphere ℂ) x) (DFunLike.coe (β := fun (x_h4 : k) ↦ Circle) ψ (GlobalTheory.Whittaker.superDiag u)) * f g) ∧ IsLocallyConstant f ∧ ∃ (C : Set (GL (Fin m) k)), IsCompact C ∧ ∀ (g : GL (Fin m) k), f g ≠ OfNat.ofNat (nat_lit 0) → ∃ (u : GL (Fin m) k), Membership.mem (γ := Subgroup (GL (Fin m) k)) (GlobalTheory.SmGL.unipB k (Fin m)) u ∧ ∃ c ∈ C, g = u * c

theorem DiscreteGroups.sglob.LConv.IsWhitTest.sub :
    ∀ {k : Type} [inst_h0 : Field k] [inst_h1 : TopologicalSpace k] {m : ℕ} {ψ : AddChar k Circle} {f f' : GL (Fin m) k → ℂ}, DiscreteGroups.sglob.LConv.IsWhitTest ψ f → DiscreteGroups.sglob.LConv.IsWhitTest ψ f' → DiscreteGroups.sglob.LConv.IsWhitTest (m := m) ψ fun (g : GL (Fin m) k) ↦ f g - f' g := by
  intro k _ _ m ψ f f' hf hf'
  unfold DiscreteGroups.sglob.LConv.IsWhitTest at hf hf' ⊢
  obtain ⟨h1, h2, C, hC, h3⟩ := hf
  obtain ⟨h1', h2', C', hC', h3'⟩ := hf'
  refine ⟨?_, h2.sub h2', C ∪ C', hC.union hC', ?_⟩
  · intro u hu g
    beta_reduce
    rw [h1 u hu g, h1' u hu g, mul_sub]
  · intro g hg
    beta_reduce at hg
    by_cases hfg : f g = 0
    · have hfg' : f' g ≠ 0 := by
        intro h
        apply hg
        rw [hfg, h, sub_zero]
      obtain ⟨u, hu, c, hc, rfl⟩ := h3' g hfg'
      exact ⟨u, hu, c, Set.mem_union_right _ hc, rfl⟩
    · obtain ⟨u, hu, c, hc, rfl⟩ := h3 g hfg
      exact ⟨u, hu, c, Set.mem_union_left _ hc, rfl⟩

end UpperTheory.Reformulated.B.P6.BlockTriangularLevi
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.DoubleSumReduceSecond
section
namespace UpperTheory.Reformulated.B.P6.r26a

open scoped HSub SubNegMonoid AddGroup AddGroupWithOne Ring HMul Distrib OfNat Zero MulZeroClass Finset Semiring Fin Complex AddCommGroup Module Module.End

noncomputable def PositivityTheory.D.DSIC.KRel :
    {n : ℕ} → {A : Type} → [inst_h0 : Ring A] → (Fin n → Bool) → (Fin n → Fin n → A) → Prop :=
  fun {n : ℕ} {A : Type} {inst_f0 : Ring A} (ε_h1 : Fin n → Bool) (F : Fin n → Fin n → A) ↦ ∀ (a b c d : Fin n), ε_h1 a = ε_h1 b → ε_h1 c = ε_h1 d → F a b * F c d - F c d * F a b = (if b = c then F a d else OfNat.ofNat (nat_lit 0)) - if d = a then F c b else OfNat.ofNat (nat_lit 0)

noncomputable def Formalism.REAL.CasK.{u_1} :
    {A : Type u_1} → [inst_h0 : Ring A] → {n : ℕ} → (Fin n → Bool) → (Fin n → Fin n → A) → A :=
  fun {A : Type u_1} {inst_f1 : Ring A} {n : ℕ} (ε_h1 : Fin n → Bool) (E : Fin n → Fin n → A) ↦ ∑ a : Fin n, ∑ b : Fin n, if ε_h1 a = ε_h1 b then E a b * E b a else OfNat.ofNat (nat_lit 0)

theorem commutator_casimir_term {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hK : PositivityTheory.D.DSIC.KRel ε E) {c d : Fin n} (hcd : ε c = ε d)
    (a b : Fin n) :
    E c d * (if ε a = ε b then E a b * E b a else 0) - (if ε a = ε b then E a b * E b a else 0) * E c d
      = ((if ε a = ε b then (if d = a then E c b * E b a else 0) else 0)
          - (if ε a = ε b then (if a = c then E a b * E b d else 0) else 0))
        + ((if ε a = ε b then (if d = b then E a b * E c a else 0) else 0)
          - (if ε a = ε b then (if b = c then E a d * E b a else 0) else 0)) := by
  by_cases h : ε a = ε b
  · simp only [if_pos h]
    have h1 : E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0) :=
      hK a b c d h hcd
    have h2 : E b a * E c d - E c d * E b a = (if a = c then E b d else 0) - (if d = b then E c a else 0) :=
      hK b a c d h.symm hcd
    have key : E c d * (E a b * E b a) - E a b * E b a * E c d
        = -((E a b * E c d - E c d * E a b) * E b a) - E a b * (E b a * E c d - E c d * E b a) := by
      noncomm_ring
    rw [key, h1, h2]
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
    abel
  · simp only [if_neg h]
    simp

theorem double_sum_reduce_first {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if d = a then E c b * E b a else 0) else 0))
      = ∑ b : Fin n, (if ε d = ε b then E c b * E b d else 0) := by
  rw [Finset.sum_eq_single d]
  · apply Finset.sum_congr rfl
    intro b _
    simp
  · intro a _ had
    apply Finset.sum_eq_zero
    intro b _
    simp [Ne.symm had]
  · intro h
    exact absurd (Finset.mem_univ d) h

theorem double_sum_reduce_fourth {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if a = c then E a b * E b d else 0) else 0))
      = ∑ b : Fin n, (if ε c = ε b then E c b * E b d else 0) := by
  rw [Finset.sum_eq_single c]
  · apply Finset.sum_congr rfl
    intro b _
    simp
  · intro a _ hac
    apply Finset.sum_eq_zero
    intro b _
    simp [hac]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem double_sum_reduce_third {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if d = b then E a b * E c a else 0) else 0))
      = ∑ a : Fin n, (if ε a = ε d then E a d * E c a else 0) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single d]
  · simp
  · intro b _ hbd
    simp [Ne.symm hbd]
  · intro h
    exact absurd (Finset.mem_univ d) h

theorem double_sum_reduce_second {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if b = c then E a d * E b a else 0) else 0))
      = ∑ a : Fin n, (if ε a = ε c then E a d * E c a else 0) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hbc
    simp [hbc]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem PositivityTheory.D.LK.casK_comm :
    ∀ {n : ℕ} {ε_h0 : Fin n → Bool} {V : Type} [inst_h2 : AddCommGroup V] [inst_h3 : _root_.Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}, PositivityTheory.D.DSIC.KRel ε_h0 E → ∀ {c d : Fin n}, ε_h0 c = ε_h0 d → Commute (E c d) (Formalism.REAL.CasK ε_h0 E) := by
  intro n ε V _ _ E hK c d hcd
  show E c d * Formalism.REAL.CasK ε E = Formalism.REAL.CasK ε E * E c d
  rw [← sub_eq_zero]
  have hsum : E c d * Formalism.REAL.CasK ε E - Formalism.REAL.CasK ε E * E c d
      = ∑ a : Fin n, ∑ b : Fin n, (E c d * (if ε a = ε b then E a b * E b a else 0)
          - (if ε a = ε b then E a b * E b a else 0) * E c d) := by
    unfold Formalism.REAL.CasK
    simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
  rw [hsum]
  simp only [commutator_casimir_term ε E hK hcd, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [double_sum_reduce_first, double_sum_reduce_fourth, double_sum_reduce_third, double_sum_reduce_second, hcd]
  simp

end UpperTheory.Reformulated.B.P6.r26a
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.EigenvectorsSumZeroEqZero
section
namespace UpperTheory.Reformulated.B.P6.r14a

theorem eigenvectors_sum_zero_eq_zero {ι κ A : Type} [DecidableEq ι] [AddCommGroup A] [Module ℂ A]
    (T : κ → Module.End ℂ A) (f : ι → κ → ℂ) (hf : Function.Injective f) :
    ∀ (s : Finset ι) (v : ι → A), (∀ i ∈ s, ∀ k, T k (v i) = f i k • v i) →
      ∑ i ∈ s, v i = 0 → ∀ i ∈ s, v i = 0 := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro v hv hsum a ha
    by_cases hall : ∀ b ∈ s, b = a
    · have h1 : ∑ i ∈ s, v i = v a := by
        apply Finset.sum_eq_single_of_mem a ha
        intro b hb hba
        exact absurd (hall b hb) hba
      rw [← h1]
      exact hsum
    · push_neg at hall
      obtain ⟨b, hb, hba⟩ := hall
      have hfb : f b ≠ f a := fun h => hba (hf h)
      obtain ⟨k, hk⟩ : ∃ k, f b k ≠ f a k := Function.ne_iff.mp hfb
      have hw_eig : ∀ i ∈ s.erase a, ∀ k', T k' ((f i k - f a k) • v i)
          = f i k' • ((f i k - f a k) • v i) := by
        intro i hi k'
        rw [map_smul, hv i (Finset.mem_of_mem_erase hi) k', smul_comm]
      have h2 : ∑ i ∈ s, (f i k - f a k) • v i = 0 := by
        have h3 : ∑ i ∈ s, (f i k - f a k) • v i
            = T k (∑ i ∈ s, v i) - f a k • ∑ i ∈ s, v i := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hv i hi k, sub_smul]
        rw [h3, hsum, map_zero, smul_zero, sub_zero]
      have hw_sum : ∑ i ∈ s.erase a, (f i k - f a k) • v i = 0 := by
        have h4 := Finset.sum_erase_add s (fun i => (f i k - f a k) • v i) ha
        simp only [sub_self, zero_smul, add_zero] at h4
        rw [h4]
        exact h2
      have hw0 := ih (s.erase a) (Finset.erase_ssubset ha)
        (fun i => (f i k - f a k) • v i) hw_eig hw_sum
      have hz : ∀ i ∈ s, f i k ≠ f a k → v i = 0 := by
        intro i hi hne
        have hia : i ≠ a := fun h => hne (by rw [h])
        have h5 : (f i k - f a k) • v i = 0 := hw0 i (Finset.mem_erase.mpr ⟨hia, hi⟩)
        rcases smul_eq_zero.mp h5 with h | h
        · exact absurd (sub_eq_zero.mp h) hne
        · exact h
      have hts : s.filter (fun i => f i k = f a k) ⊂ s := by
        rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
        exact ⟨b, hb, fun h => hk (Finset.mem_filter.mp h).2⟩
      have hsum_t : ∑ i ∈ s.filter (fun i => f i k = f a k), v i = 0 := by
        rw [Finset.sum_filter_of_ne]
        · exact hsum
        · intro i hi hvi
          by_contra hne
          exact hvi (hz i hi hne)
      exact ih _ hts v (fun i hi k' => hv i (Finset.filter_subset _ _ hi) k') hsum_t a
        (Finset.mem_filter.mpr ⟨ha, rfl⟩)

theorem GlobalTheory.CompanionTheory.PresRho.eq_zero_of_sum_weightVec :
    ∀ {ι κ A : Type} [DecidableEq ι] [inst : AddCommGroup A] [inst_1 : _root_.Module ℂ A] (T : κ → Module.End ℂ A) (f : ι → κ → ℂ), Function.Injective f → ∀ (s : Finset ι) (v : ι → A), (∀ i ∈ s, ∀ (k : κ), DFunLike.coe (T k) (v i) = f i k • v i) → ∑ i ∈ s, v i = OfNat.ofNat (nat_lit 0) → ∀ i ∈ s, v i = OfNat.ofNat (nat_lit 0) := by
  intro ι κ A _ _ _ T f hf s v hv hsum
  exact eigenvectors_sum_zero_eq_zero T f hf s v hv hsum

end UpperTheory.Reformulated.B.P6.r14a
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.EnnrealRpowTwoEqSq
section
namespace UpperTheory.Reformulated.B.P6.r96a

open scoped MeasureTheory ENNReal LE HPow NPow Monoid Semiring CommSemiring HMul Distrib OfNat

theorem ennreal_sqrt_mul_sqrt (x : ENNReal) : x ^ (1/2 : ℝ) * x ^ (1/2 : ℝ) = x := by
  calc x ^ (1/2 : ℝ) * x ^ (1/2 : ℝ) = (x ^ (1/2 : ℝ)) ^ (2:ℕ) := (sq _).symm
    _ = (x ^ (1/2 : ℝ)) ^ ((2:ℕ):ℝ) := (ENNReal.rpow_natCast _ _).symm
    _ = x := by rw [← ENNReal.rpow_mul]; norm_num

theorem ennreal_sqrt_sq (x : ENNReal) : (x ^ (1/2 : ℝ)) ^ 2 = x := by
  rw [sq]; exact ennreal_sqrt_mul_sqrt x

theorem ennreal_rpow_two_eq_sq (x : ENNReal) : x ^ (2:ℝ) = x ^ 2 := by
  rw [← ENNReal.rpow_natCast]; norm_num

theorem GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral.sq_lintegral_mul_le.{u_1} :
    ∀ {X : Type u_1} [inst_h0 : MeasurableSpace X] (ν : MeasureTheory.Measure X) {a b : X → ENNReal}, Measurable a → Measurable b → HPow.hPow (β := ℕ) (∫⁻ (w : X), a w * b w ∂ν) (OfNat.ofNat (nat_lit 2)) ≤ (∫⁻ (w : X), a w ∂ν) * ∫⁻ (w : X), a w * HPow.hPow (β := ℕ) (b w) (OfNat.ofNat (nat_lit 2)) ∂ν := by
  intro X _ ν a b ha hb
  have hf : AEMeasurable (fun w => a w ^ (1/2:ℝ)) ν := (ha.pow_const _).aemeasurable
  have hg : AEMeasurable (fun w => a w ^ (1/2:ℝ) * b w) ν := ((ha.pow_const _).mul hb).aemeasurable
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq ν (p := 2) (q := 2)
    Real.HolderConjugate.two_two hf hg
  have key2 : ∫⁻ w, a w * b w ∂ν ≤
      (∫⁻ w, a w ∂ν) ^ (1/(2:ℝ)) * (∫⁻ w, a w * b w ^ 2 ∂ν) ^ (1/(2:ℝ)) := by
    have h1 : ∫⁻ w, a w * b w ∂ν
        = ∫⁻ w, ((fun w => a w ^ (1/2:ℝ)) * (fun w => a w ^ (1/2:ℝ) * b w)) w ∂ν := by
      apply MeasureTheory.lintegral_congr
      intro w
      simp only [Pi.mul_apply]
      rw [← mul_assoc, ennreal_sqrt_mul_sqrt]
    have h2 : ∫⁻ w, a w ∂ν = ∫⁻ w, (a w ^ (1/2:ℝ)) ^ (2:ℝ) ∂ν := by
      apply MeasureTheory.lintegral_congr
      intro w
      rw [ennreal_rpow_two_eq_sq, ennreal_sqrt_sq]
    have h3 : ∫⁻ w, a w * b w ^ 2 ∂ν = ∫⁻ w, (a w ^ (1/2:ℝ) * b w) ^ (2:ℝ) ∂ν := by
      apply MeasureTheory.lintegral_congr
      intro w
      rw [ennreal_rpow_two_eq_sq, mul_pow, ennreal_sqrt_sq]
    rw [h1, h2, h3]
    exact key
  calc (∫⁻ w, a w * b w ∂ν) ^ 2
      ≤ ((∫⁻ w, a w ∂ν) ^ (1/(2:ℝ)) * (∫⁻ w, a w * b w ^ 2 ∂ν) ^ (1/(2:ℝ))) ^ 2 := by
        gcongr
    _ = (∫⁻ w, a w ∂ν) * ∫⁻ w, a w * b w ^ 2 ∂ν := by
        rw [mul_pow, ennreal_sqrt_sq, ennreal_sqrt_sq]

end UpperTheory.Reformulated.B.P6.r96a
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.ExistsEquivInnerOfNondegenerate
section
namespace UpperTheory.Reformulated.B.P6.r12b
open FourierTransform MeasureTheory Complex Real Module

theorem integral_comp_linearEquiv_eq_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (e : V ≃L[ℝ] E) :
    ∃ c : NNReal, ∀ F : E → ℂ, ∫ v, F (e v) ∂μ = c • ∫ w, F w := by
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ.map e = c • (volume : Measure E) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun F => ?_⟩
  have h1 : ∫ v, F (e v) ∂μ = ∫ w, F w ∂(μ.map e) := by
    have := integral_map_equiv (μ := μ) e.toHomeomorph.toMeasurableEquiv F
    simpa using this.symm
  rw [h1, hc, integral_smul_nnreal_measure]

theorem exists_equiv_inner_of_nondegenerate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ u, (∀ v, B u v = 0) → u = 0) (e : V ≃L[ℝ] E) :
    ∃ A : V ≃L[ℝ] E, ∀ u v, B u v = inner ℝ (A u) (e v) := by
  let L : V →ₗ[ℝ] E →ₗ[ℝ] ℝ := B.compl₂ (e.symm : E →ₗ[ℝ] V)
  let Φ : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := innerₗ E
  have hΦ : ∀ x y, Φ x y = inner ℝ x y := fun x y => by simp [Φ]
  have hΦi : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : inner ℝ x x = (0 : ℝ) := by rw [← hΦ, hx]; rfl
    exact inner_self_eq_zero.mp h0
  have hdim : finrank ℝ E = finrank ℝ (E →ₗ[ℝ] ℝ) := (Subspace.dual_finrank_eq).symm
  have hΦs : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hΦi
  let Φe : E ≃ₗ[ℝ] (E →ₗ[ℝ] ℝ) := LinearEquiv.ofBijective Φ ⟨hΦi, hΦs⟩
  have hΦe : ∀ x, Φe x = Φ x := fun x => rfl
  let a : V →ₗ[ℝ] E := Φe.symm.toLinearMap ∘ₗ L
  have ha : ∀ u w, inner ℝ (a u) w = B u (e.symm w) := by
    intro u w
    rw [← hΦ, ← hΦe]
    simp [a, L]
  have hai : Function.Injective a := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    apply hB u
    intro v
    have := ha u (e v)
    rw [hu, inner_zero_left, e.symm_apply_apply] at this
    exact this.symm
  have hdim2 : finrank ℝ V = finrank ℝ E := e.toLinearEquiv.finrank_eq
  have has : Function.Surjective a :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim2).mp hai
  let A : V ≃L[ℝ] E := (LinearEquiv.ofBijective a ⟨hai, has⟩).toContinuousLinearEquiv
  refine ⟨A, fun u v => ?_⟩
  have hA : A u = a u := rfl
  rw [hA, ha, e.symm_apply_apply]

theorem GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_bilinear_transform.{u_1} :
    ∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [FiniteDimensional ℝ V] [inst_3 : MeasurableSpace V] [BorelSpace V] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ (u : V), (∀ (v : V), DFunLike.coe (DFunLike.coe B u) v = OfNat.ofNat (nat_lit 0)) → u = OfNat.ofNat (nat_lit 0)) → ∀ (φ : SchwartzMap V ℂ), ∃ (ψ : SchwartzMap V ℂ), DFunLike.coe ψ = fun (u : V) ↦ ∫ (v : V), Complex.exp (OfNat.ofNat (nat_lit 2) * Complex.ofReal Real.pi * Complex.I * Complex.ofReal (DFunLike.coe (DFunLike.coe B u) v)) * DFunLike.coe φ v ∂μ := by
  intro V _ _ _ _ _ μ _ B hB φ
  let E := EuclideanSpace ℝ (Fin (finrank ℝ V))
  let e : V ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [E])
  obtain ⟨A, hA⟩ := exists_equiv_inner_of_nondegenerate B hB e
  obtain ⟨c, hc⟩ := integral_comp_linearEquiv_eq_smul μ e
  let g : SchwartzMap E ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm φ
  have hg : ∀ w, g w = φ (e.symm w) := fun w => rfl
  let N : V ≃L[ℝ] E := A.trans (ContinuousLinearEquiv.neg ℝ)
  let h : SchwartzMap V ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ N (𝓕 g)
  have hh : ∀ u, h u = (𝓕 g) (-(A u)) := fun u => rfl
  refine ⟨((c : ℝ) : ℂ) • h, ?_⟩
  funext u
  have hF : ∀ w : E, (𝓕 g) w = ∫ x, Complex.exp (-(2 * π * I * (inner ℝ x w : ℝ))) * g x := by
    intro w
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    congr 1; ext x
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    congr 1; push_cast; ring_nf
  let F : E → ℂ := fun w => Complex.exp (2 * π * I * (inner ℝ (A u) w : ℝ)) * φ (e.symm w)
  have hint : (fun v => Complex.exp (2 * π * I * ((B u v : ℝ) : ℂ)) * φ v) = fun v => F (e v) := by
    funext v
    simp only [F, hA, e.symm_apply_apply]
  have hL : (((c : ℝ) : ℂ) • h) u = ((c : ℝ) : ℂ) * ∫ w, F w := by
    rw [SchwartzMap.smul_apply, hh, hF, smul_eq_mul]
    congr 1
    congr 1; ext x
    rw [hg, inner_neg_right, real_inner_comm]
    congr 2
    push_cast; ring
  rw [hL]
  show _ = ∫ v, Complex.exp (2 * π * I * ((B u v : ℝ) : ℂ)) * φ v ∂μ
  rw [hint, hc F, NNReal.smul_def, Complex.real_smul]

end UpperTheory.Reformulated.B.P6.r12b
end

