module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Classical

noncomputable section
namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

section Vertex
variable (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c : ℕ)

def symN : Subgroup (GL (n ⊕ Fin c) k) := N k n c ((c + 1) / 2) ⊔ N k n c (c / 2 + 1)

def symR : Subgroup (GL (n ⊕ Fin c) k) := (embX c).range ⊔ symN k n c

theorem symN_odd (ρ : ℕ) : symN k n (2 * ρ + 1) = N k n (2 * ρ + 1) (ρ + 1) := by
  rw [symN, show (2 * ρ + 1 + 1) / 2 = ρ + 1 by omega, show (2 * ρ + 1) / 2 + 1 = ρ + 1 by omega, sup_idem]

theorem symN_even (ρ : ℕ) : symN k n (2 * ρ) = N k n (2 * ρ) ρ ⊔ N k n (2 * ρ) (ρ + 1) := by
  rw [symN, show (2 * ρ + 1) / 2 = ρ by omega, show 2 * ρ / 2 + 1 = ρ + 1 by omega]

variable {k n c}

theorem symN_conj {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) (g : GL n k) :
    (embX c g)⁻¹ * u * embX c g ∈ symN k n c := by
  have h : symN k n c ≤ (symN k n c).comap (MulAut.conj (embX c g)⁻¹).toMonoidHom :=
    sup_le (fun v hv => Subgroup.mem_sup_left (by simpa using RootEx.Model.conj_mem hv g))
      fun v hv => Subgroup.mem_sup_right (by simpa using RootEx.Model.conj_mem hv g)
  simpa using h hu

def symPr (C : Subgroup (GL (n ⊕ Fin c) k)) : Subgroup (GL n k) where
  carrier := {g | ∃ u ∈ symN k n c, u * embX c g ∈ C}
  one_mem' := ⟨1, one_mem _, by simp⟩
  mul_mem' := by
    rintro g g' ⟨u, hu, h⟩ ⟨u', hu', h'⟩
    refine ⟨u * ((embX c g⁻¹)⁻¹ * u' * embX c g⁻¹), mul_mem hu (symN_conj hu' g⁻¹), ?_⟩
    convert C.mul_mem h h' using 1
    simp [mul_assoc]
  inv_mem' := by
    rintro g ⟨u, hu, h⟩
    refine ⟨(embX c g)⁻¹ * u⁻¹ * embX c g, symN_conj (inv_mem hu) g, ?_⟩
    convert C.inv_mem h using 1
    simp [mul_assoc]

variable {n' : Type*} [Fintype n'] [DecidableEq n']

def Kept : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → Prop
  | (Sum.inl _, Sum.inr i) => Even c ∧ i.val = c / 2
  | (Sum.inr l, Sum.inl _) => Odd c ∧ l.val = c / 2
  | _ => False


omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem Kept.not_free {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} (h : Kept rs) : ¬ Free (c / 2 + 1) rs := by
  rcases rs with ⟨r | r, s | s⟩ <;> simp only [Kept, Free] at h ⊢ <;> omega


variable (n n' c) in
abbrev StepVar (n : Type*) (c : ℕ) (n' : Type*) : Type _ :=
  {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (c / 2 + 1) rs ∨ Kept rs}


open Classical in
def stepPt (x₀ : Matrix n n' k) (e : StepVar n c n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  basePt c x₀ + Matrix.of fun r s => if h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s) then e ⟨(r, s), h⟩ else 0


open Classical in
def keptPt (w : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Kept rs} → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => if h : Kept (r, s) then w ⟨(r, s), h⟩ else 0


omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem stepPt_eq (x₀ : Matrix n n' k) (e : StepVar n c n' → k) : stepPt x₀ e =
    affPt (c / 2 + 1) x₀ (fun rs => e ⟨rs.1, Or.inl rs.2⟩) + keptPt fun rs => e ⟨rs.1, Or.inr rs.2⟩ := by
  ext r s
  by_cases h : Kept (r, s)
  · simp [stepPt, affPt, keptPt, h, h.not_free]
  · by_cases h' : Free (c / 2 + 1) (r, s) <;> simp [stepPt, affPt, keptPt, h, h']

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def flatStep [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k)
    (w : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Kept rs} → k) : ℂ :=
  opE ψ ν (c / 2 + 1) (fun x => Φ (x + keptPt w)) x₀

def invVol (C : Subgroup (GL (n ⊕ Fin c) k)) : ℚ :=
  (C.relIndex (symN k n c ⊓ KO k _) : ℚ) / (KO k _).relIndex (symN k n c ⊓ C)

theorem relIndex_ne_zero_of_isOpen {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {U K H : Subgroup G} (hU : IsOpen (U : Set G)) (hK : IsCompact (K : Set G)) (hH : H ≤ K) : U.relIndex H ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  exact fun h => Subgroup.index_ne_zero_of_finite (Subgroup.relIndex_eq_zero_of_le_right hH h)

theorem invVol_KO : invVol (KO k (n ⊕ Fin c)) = 1 := by
  simp [invVol, Subgroup.relIndex_eq_one.2 inf_le_right]

end Vertex

variable {k : Type*} [Field k] (G : Grid (k := k))

def topRank (j : ℕ) : ℕ := G.r + 1 + G.m * (G.s - 1) + j * (G.t + 1)


variable {G} in
theorem topRank_add (hs : 1 ≤ G.s) (j : ℕ) : topRank G j + G.m = G.rank (G.m, j) + j + 1 := by
  obtain ⟨s, h⟩ := Nat.exists_eq_add_of_le' hs
  simp only [topRank, Grid.rank, h, Nat.add_sub_cancel]; ring

def frame {a c b : ℕ} (h : a + c = b) : Fin a ⊕ Fin c ≃ Fin b := finSumFinEquiv.trans (finCongr h)

def frameGL {a c b : ℕ} (h : a + c = b) : GL (Fin b) k ≃* GL (Fin a ⊕ Fin c) k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k (frame h).symm).toMulEquiv

abbrev ColArgs : Type _ := ∀ j : ℕ, Matrix (Fin (topRank G (j + 1))) (Fin (topRank G j)) k

abbrev RowArgs : Type _ := ∀ i : ℕ, Matrix (Fin (G.rank (i, G.m))) (Fin (G.rank (i + 1, G.m))) k

abbrev Vars : Type _ :=
  ∀ j : Fin (G.m - 1), StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)) → k

def topLast (j : ℕ) : Fin (topRank G j) := ⟨topRank G j - 1, by unfold topRank; omega⟩

variable {G}

def colVar (x : ColArgs G) (e : Vars G) (j : Fin (G.m - 1)) (r : Fin (topRank G (j + 1))) : k :=
  stepPt (x j) (e j) (.inl r) (.inr ⟨(G.m - 2 - j) / 2, by omega⟩)

def rowVar (x : ColArgs G) (e : Vars G) (j : ℕ) (s : Fin (topRank G j)) : k :=
  if h : j < G.m - 1 then ∑ l : Fin (G.m - 2 - j),
    if l.val = (G.m - 2 - j) / 2 then stepPt (x j) (e ⟨j, h⟩) (.inr l) (.inl s) else 0
  else x j (topLast G (j + 1)) s

def phase (x : ColArgs G) (e : Vars G) : k :=
  ∑ j : Fin (G.m - 1), (ch (stepPt (x j) (e j)) +
    if Even (G.m - 2 - j) then ∑ r, rowVar x e (j + 1) r * colVar x e j r else 0)

variable (hs : 1 ≤ G.s)

def downMap (x : ColArgs G) (e : Vars G) (j : ℕ) : Matrix (Fin (G.rank (G.m, j + 1))) (Fin (G.rank (G.m, j))) k :=
  if h : j < G.m - 1 then
    (stepPt (c := G.m - 2 - j) (x j) (e ⟨j, h⟩)).reindex (frame (by have := topRank_add hs (j + 1); omega))
      (frame (by have := topRank_add hs j; omega))
  else if h' : j + 1 = G.m then
    (x j).submatrix (Fin.castLE (by have := topRank_add hs (j + 1); omega))
      (Fin.cast (by have := topRank_add hs j; omega))
  else 0

def fill (x : ColArgs G) (y : RowArgs G) (e : Vars G) : G.Args
  | .theta i j => if h : i = G.m then ((downMap hs x e j).submatrix (Fin.cast (by rw [h])) (Fin.cast (by rw [h])))ᵀ else 0
  | .ex i j => if h : j = G.m then ((y i).submatrix (Fin.cast (by rw [h])) (Fin.cast (by rw [h])))ᵀ else 0

theorem fill_theta (x : ColArgs G) (y : RowArgs G) (e : Vars G) (j : ℕ) :
    fill hs x y e (.theta G.m j) = (downMap hs x e j)ᵀ := dite_eq_left rfl

theorem fill_ex (x : ColArgs G) (y : RowArgs G) (e : Vars G) (i : ℕ) : fill hs x y e (.ex i G.m) = (y i)ᵀ :=
  dite_eq_left rfl

def toFrame {j : ℕ} (hj : j < G.m) :
    GL (Fin (G.rank (G.m, j))) k ≃* GL (Fin (topRank G j) ⊕ Fin (G.m - 1 - j)) k :=
  frameGL (by have := topRank_add hs j; omega)

def rowR {j : ℕ} (hj : j < G.m) : Subgroup (GL (Fin (G.rank (G.m, j))) k) :=
  (symR k _ _).comap (toFrame hs hj).toMonoidHom

def conjLevel (J : G.Level) (g : G.VertexGroup) {j : ℕ} (hj : j < G.m) :
    Subgroup (GL (Fin (topRank G j) ⊕ Fin (G.m - 1 - j)) k) :=
  ((J (G.m, j)).map (MulAut.conj (g (G.m, j))).toMonoidHom).map (toFrame hs hj).toMonoidHom

abbrev Cosets (J : G.Level) : Type _ := ∀ i : Fin (G.m - 2),
  DoubleCoset.Quotient (rowR hs (j := i + 1) (by omega) : Set (GL (Fin (G.rank (G.m, i + 1))) k)) (J (G.m, i + 1))

structure Reps (J : G.Level) where

  base : GL (Fin (G.rank (G.m, 0))) k

  rep : ∀ i : Fin (G.m - 2), DoubleCoset.Quotient (rowR hs (j := i + 1) (by omega) :
    Set (GL (Fin (G.rank (G.m, i + 1))) k)) (J (G.m, i + 1)) → GL (Fin (G.rank (G.m, i + 1))) k
  mk_rep : ∀ i β, DoubleCoset.mk _ _ (rep i β) = β

def onColumn (h : ∀ j : ℕ, GL (Fin (G.rank (G.m, j))) k) : G.VertexGroup := fun X =>
  if hi : X.1 = G.m then (show (G.m, X.2) = X from hi ▸ rfl) ▸ h X.2 else 1

theorem onColumn_apply (h : ∀ j : ℕ, GL (Fin (G.rank (G.m, j))) k) (j : ℕ) : onColumn h (G.m, j) = h j := dite_eq_left rfl

variable {hs}

def Reps.elt {J : G.Level} (ρ : Reps hs J) (β : Cosets hs J) : G.VertexGroup := onColumn fun
  | 0 => ρ.base
  | i + 1 => if h : i < G.m - 2 then ρ.rep ⟨i, h⟩ (β ⟨i, h⟩) else 1


variable (hs) in
open Classical in
def Reps.through (J : G.Level) (h : ∀ j : ℕ, GL (Fin (G.rank (G.m, j))) k) : Reps hs J where
  base := h 0
  rep i β := if DoubleCoset.mk _ _ (h (i + 1)) = β then h (i + 1) else β.out
  mk_rep i β := by
    split_ifs with H
    · exact H
    · exact DoubleCoset.out_eq' β


variable (G) in
def stair (ϖ : kˣ) (e j : ℕ) : GL (Fin (G.rank (G.m, j))) k := diagGL fun a => ϖ ^ (e * (a.val + 1 - topRank G j))

theorem toFrame_stair (ϖ : kˣ) (e : ℕ) {j : ℕ} (hj : j < G.m) : toFrame hs hj (stair G ϖ e j) =
    diagGL (Sum.elim (fun _ => 1) fun p => ϖ ^ (e * (p.val + 1))) := by
  refine Units.ext ?_
  have h : topRank G j + (G.m - 1 - j) = G.rank (G.m, j) := by have := topRank_add hs j; omega
  show (stair G ϖ e j).val.submatrix (frame h) (frame h) = _
  rw [stair, diagGL_val, diagGL_val, submatrix_diagonal_equiv]
  congr 1
  funext x
  rcases x with a | p
  · simp [frame, Nat.sub_eq_zero_of_le (Nat.succ_le_of_lt a.2)]
  · simp [frame, add_assoc]


variable (G) in
structure UnfTerm where

  coef : ℚ

  datum : ColArgs G → RowArgs G → ℂ

  pr : ∀ j : ℕ, 0 < j → j < G.m → Subgroup (GL (Fin (topRank G j)) k)

  row : ∀ i : ℕ, Subgroup (GL (Fin (G.rank (i, G.m))) k)

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (G) in
def charFactor (g : G.VertexGroup) : ℂˣ :=
  ((oppositePath G.m).map fun b => G.kappa b b.src (gdet (g b.src)) * (G.kappa b b.tgt (gdet (g b.tgt)))⁻¹).prod


variable (G) in
def moved (keep : Bool) (g : G.VertexGroup) (T : G.Args → ℂ) : G.Args → ℂ := fun z =>
  (if keep then (1 : ℂ) else (((charFactor G g)⁻¹ : ℂˣ) : ℂ)) * G.pathAct .one (oppositePath G.m) g T z

theorem moved_false (g : G.VertexGroup) (T : G.Args → ℂ) (z : G.Args) : moved G false g T z =
    ((oppositePath G.m).map fun b => apow (gdet (g b.src))⁻¹ ((G.rank b.tgt : ℂ) / 2) *
      apow (gdet (g b.tgt))⁻¹ (-(G.rank b.src : ℂ) / 2)).prod * T (G.moveArgs .one g z) := by
  simp only [moved, Grid.pathAct, charFactor, ← mul_assoc]
  congr 1
  induction oppositePath G.m with
  | nil => simp
  | cons b γ ih =>
    simp only [List.map_cons, List.prod_cons, ← ih, Grid.edgeFactor, Assignment.read, gdet_invT]
    simp only [Bool.false_eq_true, ite_false, _root_.mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp

variable (hs) [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)


def flatIntegrand (S : G.Args → ℂ) (x : ColArgs G) (y : RowArgs G) (e : Vars G) : ℂ :=
  S (fill hs x y e) * (ψ (-phase x e) : ℂ)


variable (G) in
def varsVol : Measure (Vars G) := Measure.pi fun _ => Measure.pi fun _ => ν


def flatTensor (S : G.Args → ℂ) (x : ColArgs G) (y : RowArgs G) : ℂ :=
  ∫ e, flatIntegrand hs ψ S x y e ∂(varsVol G ν)


def FlatIntegrable (T : G.Args → ℂ) : Prop :=
  ∀ g x y, Integrable (flatIntegrand hs ψ (moved G true g T) x y) (varsVol G ν)

variable {hs} {J : G.Level} (keep : Bool) (ρ : Reps hs J) (T : G.Args → ℂ)

def unfTerm (β : Cosets hs J) : UnfTerm G where
  coef := ∏ i : Fin (G.m - 2), invVol (conjLevel hs J (ρ.elt β) (j := i + 1) (by omega))
  datum := flatTensor hs ψ ν (moved G keep (ρ.elt β) T)
  pr _ _ hj := symPr (conjLevel hs J (ρ.elt β) hj)
  row i := J (i, G.m)

def unfSupport : Set (Cosets hs J) := {β | (unfTerm ψ ν keep ρ T β).datum ≠ 0}

def unf (hfin : (unfSupport ψ ν keep ρ T).Finite) : Multiset (UnfTerm G) :=
  hfin.toFinset.val.map (unfTerm ψ ν keep ρ T)



variable (hs J) in
def OneCoset (ϖ : kˣ) (e : ℕ) : Prop :=
  ∀ β ∈ unfSupport ψ ν false (Reps.through hs J (stair G ϖ e)) T, ∀ i, β i = DoubleCoset.mk _ _ (stair G ϖ e (i + 1))

theorem through_elt (h : ∀ j : ℕ, GL (Fin (G.rank (G.m, j))) k) {j : ℕ} (hj : j + 2 ≤ G.m) :
    (Reps.through hs J h).elt (fun i => DoubleCoset.mk _ _ (h (i + 1))) (G.m, j) = h j := by
  rw [Reps.elt, onColumn_apply]
  cases j with
  | zero => rfl
  | succ i => simp [Reps.through, show i < G.m - 2 by omega]


end GlobalTheory.FunObj
