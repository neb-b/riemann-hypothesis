module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalOverDiagonalDoubleCosetReps
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRead
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.FlatFactor

section Gen
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

def fill (ev it : Finset (m × m')) (β t : Matrix m m' k) (a : {e : m × m' // e ∈ it} → k) : Matrix m m' k :=
  Matrix.of fun r q => if h : (r, q) ∈ it then a ⟨(r, q), h⟩ else if (r, q) ∈ ev then β r q else t r q

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

def red (ν : Measure k) (ev it : Finset (m × m')) (β : Matrix m m' k) (Θ : Matrix m m' k → ℂ) (t : Matrix m m' k) : ℂ :=
  ∫ a, Θ (fill ev it β t a) ∂(Measure.pi fun _ => ν)

def KerRed {M : Type} [AddCommGroup M] [Module ℂ M] (ν : Measure k) (ev it : Finset (m × m')) (β : Matrix m m' k)
    (l : SB (Matrix m m' k) →ₗ[ℂ] M) : Prop :=
  ∀ Θ : SB (Matrix m m' k), (∀ t, red ν ev it β Θ.1 t = 0) → l Θ = 0

end Gen

section Pos
variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ)


open Classical in
def evC : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e =>
    (∃ i, e.2 = Sum.inr i ∧ i.val < ρ ∧ ¬ Free (ρ + 1) e) ∨
    (∃ l, e.1 = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, e.2 = Sum.inr i → i.val = ρ)


open Classical in
def itB : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ ≤ i.val

def IsRead : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → Prop
  | (.inl _, .inl _) => True
  | (.inl _, .inr i) => i.val = ρ
  | (.inr _, _) => False


open Classical in
def evAll : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => ¬ Free (ρ + 1) e ∧ ¬ IsRead n n' c ρ e


open Classical in
def itFree : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e

variable {n n' c}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def TwLaw {M : Type} [AddCommGroup M] [Module ℂ M] (ψ : AddChar k Circle)
    (l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M) : Prop :=
  ∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → (∀ i j : Fin c, i.val < ρ → ρ ≤ j.val → u.val i j = 0) →
    ∀ Θ Θ' Θ'' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      (∀ t, Θ'.1 t = Θ.1 (((embA n u)⁻¹).val * t)) →
      (∀ t, Θ''.1 t = (ψ (ch ((embA n u).val * t) - ch t) : ℂ) * Θ.1 t) →
      l Θ' = (ψ (-simpleSum (embA n u)) : ℂ) • l Θ''

end Pos

end GlobalTheory.FlatFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelsCommuteExplicitConst
section
open ValuativeRel IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.KernelCommTw

noncomputable section

namespace GlobalTheory.KernelCommExplicit

theorem kernelsCommuteExplicitConst : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (l' l : kˣ →* ℂˣ), IsUnram l' → IsUnram l → ∀ (P₀ : Pair k n') (Q₀ : Pair k n), ∀ (V' V : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V] (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V) (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V), (∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)), (∀ x, Ψ'.1 x = (l' (Matrix.GeneralLinearGroup.det g) : ℂ) * (l (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (π' g v) Ψ' = π h (θ v Ψ)) → ∃ K : EqForm π' →ₗ[ℂ] EqForm π, (∀ φ, (K φ).1 Q₀ = θ (φ.1 P₀) (phiOneSB P₀ Q₀)) ∧ (∀ (s : 𝓀[k]ˣ) φ, (K ⟨dia s φ.1, dia_mem_EqForm s φ.2⟩).1 = dia s (K φ).1) ∧ ∀ φ : EqForm π', φ.1 ∈ Mram k n' V' → (K φ).1 ∈ Mram k n V ∧ (K ⟨FFStar q (resChar ψ hψ q) φ.1, FFStar_mem_EqForm q _ φ.2⟩).1 = ((l' q.unit : ℂ) * (l q.unit : ℂ)) • FFStar q (resChar ψ hψ q) (K φ).1 := by
  intro k _ _ _ _ n n' _ _ _ _ q ψ hψ l' l hl' hl P₀ Q₀ V' V _ _ _ _ π' π θ hθ
  refine ⟨LinearMap.codRestrict (EqForm π) (KK hl hθ P₀ Q₀ ∘ₗ (EqForm π').subtype)
    fun φ => KK_mem hl hθ P₀ Q₀ φ.1, fun φ => ?_, fun s φ => KK_dia hl hθ P₀ Q₀ hl' s φ.2, fun φ h =>
      ⟨KK_ram hl hθ P₀ Q₀ hl' φ.2 h, KK_FFStar hl hθ P₀ Q₀ hl' q _ φ.2 h⟩⟩
  show KK hl hθ P₀ Q₀ φ.1 Q₀ = _
  simpa using KK_smul hl hθ P₀ Q₀ φ.1 1

end GlobalTheory.KernelCommExplicit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroUniformizerFrameUnipotentAndEmbedGL
section
open ValuativeRel Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.LevZeroUp
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LevZeroGen GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

def scal (ϖ : kˣ) : XIx (Fin κ) t 0 ⊕ Fin (s + 1) → k := Sum.elim 1 fun i => (ϖ : k) ^ (i.val + 1)

def back : XIx (Fin κ) t 0 ⊕ Fin (s + 1) → Fin κ ⊕ Fin (s + 1) :=
  fun r => (ixZero (Fin κ ⊕ Fin (s + 1)) t).symm ((stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)).symm r)

theorem back_eps (i : Fin κ) : back (s := s) t (.inl (.inl (.inl i))) = .inl i := by
  unfold back
  rw [show (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)).symm (.inl (.inl (.inl i))) = .inl (.inl i) from
    (Equiv.symm_apply_eq _).2 rfl]
  exact (Equiv.symm_apply_eq _).2 rfl

theorem levelZeroOldIndexOfNew_inr (i : Fin (s + 1)) : back (κ := κ) t (.inr i) = .inr i := by
  unfold back
  rw [show (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)).symm (.inr i) = .inl (.inr i) from
    (Equiv.symm_apply_eq _).2 (standardOrderExtendedBasis_apply_low_block (Fin κ) t (l := s + 1) 0 (s + 1) (Nat.zero_add _) i).symm]
  exact (Equiv.symm_apply_eq _).2 rfl

theorem scal_ne_zero (ϖ : kˣ) (r : XIx (Fin κ) t 0 ⊕ Fin (s + 1)) : scal t ϖ r ≠ 0 := by
  rcases r with r | r <;> simp [scal]

theorem bas_val : ((S.T t).bas 0 (s + 1) (Nat.zero_add _)).val = diagonal (scal t S.ϖ) := by
  show (embA _ (SplitFlip.diagGL fun i : Fin (s + 1) => S.ϖ ^ (i.val + 1))).val = _
  simp only [embA, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk, SplitFlip.diagGL_val]
  rw [← diagonal_one, fromBlocks_diagonal]
  congr 1

theorem bas_inv_val : (((S.T t).bas 0 (s + 1) (Nat.zero_add _))⁻¹).val = diagonal fun r => (scal t S.ϖ r)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [bas_val, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext r; exact mul_inv_cancel₀ (scal_ne_zero t S.ϖ r)

theorem upZero_entry (x : GL (Fin κ ⊕ Fin (s + 1)) k) (r c : XIx (Fin κ) t 0 ⊕ Fin (s + 1)) :
    (upZero S t x).val r c = scal t S.ϖ r * x.val (back t r) (back t c) * (scal t S.ϖ c)⁻¹ := by
  rw [upZero_apply, Units.val_mul, Units.val_mul, bas_val, bas_inv_val, mul_diagonal, diagonal_mul, reGL_val, reGL_val]
  rfl

theorem xZero_symm (i : Fin κ) : (xZero (Fin κ) t).symm (.inl (.inl i)) = i := (Equiv.symm_apply_eq _).2 rfl

theorem upZero_mem_N {n : GL (Fin κ ⊕ Fin (s + 1)) k} (hn : n ∈ N k (Fin κ) (s + 1) (S.ρ + 1)) :
    upZero S t n ∈ N k (XIx (Fin κ) t 0) (s + 1) (S.ρ + 1) := by
  rw [Model.mem_N_iff] at hn ⊢
  intro r c h
  rw [upZero_entry]
  rcases r with ((r | r) | ⟨r, _⟩) | r
  · rcases c with ((c | c) | ⟨c, _⟩) | c
    · rw [back_eps, back_eps, hn _ _ (by simp [lev])]
      by_cases e : r = c
      · subst e; simp [scal]
      · simp [scal, Matrix.one_apply, e]
    · exact c.elim0
    · exact c.elim0
    · rw [back_eps, levelZeroOldIndexOfNew_inr, hn _ _ (by simpa [lev] using h)]
      simp [Matrix.one_apply]
  · exact r.elim0
  · exact r.elim0
  · rcases c with ((c | c) | ⟨c, _⟩) | c
    · rw [back_eps, levelZeroOldIndexOfNew_inr, hn _ _ (by simpa [lev] using h)]
      simp [Matrix.one_apply]
    · exact c.elim0
    · exact c.elim0
    · rw [levelZeroOldIndexOfNew_inr, levelZeroOldIndexOfNew_inr, hn _ _ (by simpa [lev] using h)]
      by_cases e : r = c
      · subst e; simp [scal, Matrix.one_apply]
      · simp [Matrix.one_apply, e]

theorem simpleSum_upZero (n : GL (Fin κ ⊕ Fin (s + 1)) k) :
    simpleSum (upZero S t n) = ((S.ϖ⁻¹ : kˣ) : k) * simpleSum n := by
  have hϖ : (S.ϖ : k) ≠ 0 := S.ϖ.ne_zero
  unfold simpleSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [upZero_entry, levelZeroOldIndexOfNew_inr, levelZeroOldIndexOfNew_inr]
    simp only [scal, Sum.elim_inr, h, Units.val_inv_eq_inv_val]
    field_simp
    ring
  · simp

theorem superSum_one : superSum Fin.val (1 : Matrix (Fin κ) (Fin κ) k) = 0 := by
  unfold superSum
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · have : i ≠ j := by rintro rfl; omega
    simp [Matrix.one_apply, this]
  · rfl

theorem lam_eq (n : S.P.J) (hn : n.1 ∈ N k (Fin κ) (s + 1) (S.ρ + 1)) :
    ((S.P.lam n : ℂˣ) : ℂ) = (S.ψ (simpleSum (upZero S t n.1)) : ℂ) := by
  rw [S.sym.2 n, simpleSum_upZero]
  have h11 : (n : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁ = 1 := by
    rw [Model.mem_N_iff] at hn
    ext i j
    simpa [toBlocks₁₁, Matrix.one_apply] using hn (.inl i) (.inl j) (by simp [lev])
  rw [h11, superSum_one]
  simp

theorem upZero_embX (γ : GL (Fin κ) k) :
    upZero S t (embX (s + 1) γ) = embX (s + 1) (reGL (xZero (Fin κ) t) γ) := by
  ext r c
  rw [upZero_entry]
  rcases r with ((r | r) | ⟨r, _⟩) | r
  · rcases c with ((c | c) | ⟨c, _⟩) | c
    · rw [back_eps, back_eps]
      simp [embX, scal, reGL_val, xZero_symm]
    · exact c.elim0
    · exact c.elim0
    · rw [back_eps, levelZeroOldIndexOfNew_inr]
      simp [embX]
  · exact r.elim0
  · exact r.elim0
  · rcases c with ((c | c) | ⟨c, _⟩) | c
    · rw [levelZeroOldIndexOfNew_inr, back_eps]
      simp [embX]
    · exact c.elim0
    · exact c.elim0
    · rw [levelZeroOldIndexOfNew_inr, levelZeroOldIndexOfNew_inr]
      by_cases e : r = c
      · subst e; simp [embX, scal, Matrix.one_apply]
      · simp [embX, Matrix.one_apply, e]

theorem upZero_N_embX : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], (∀ n : S.P.J, n.1 ∈ GlobalTheory.RootEx.N k (Fin κ) (s + 1) (S.ρ + 1) → GlobalTheory.LevZeroGen.upZero S t n.1 ∈ GlobalTheory.RootEx.N k (GlobalTheory.StepData.XIx (Fin κ) t 0) (s + 1) (S.ρ + 1) ∧ ((S.P.lam n : ℂˣ) : ℂ) = (S.ψ (GlobalTheory.RootEx.simpleSum (GlobalTheory.LevZeroGen.upZero S t n.1)) : ℂ)) ∧ ∀ γ : GL (Fin κ) k, GlobalTheory.LevZeroGen.upZero S t (GlobalTheory.RootEx.embX (s + 1) γ) = GlobalTheory.RootEx.embX (s + 1) (GlobalTheory.StepData.reGL (GlobalTheory.LevZeroGen.xZero (Fin κ) t) γ) := by
  intro k _ _ _ _ s κ S t _ _
  exact ⟨fun n hn => ⟨upZero_mem_N S t hn, lam_eq S t n hn⟩, upZero_embX S t⟩

end GlobalTheory.LevZeroUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixBlockColumnVanishingStep
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain.ExchangeCol

section SlopeTestRemainingChoices
variable {k : Type} [Field k] {ι ι' n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

theorem coords_typeFrame_apply (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) (o' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (a : ι) (b : ι') :
    (typeFrame ϖ o).coords (typeFrame ϖ o') x a b =
      Sum.elim (fun _ => 1) (fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) (o a) * x (o a) (o' b) *
        Sum.elim (fun _ => 1) (fun i : Fin c' => (ϖ : k) ^ (i.val + 1)) (o' b) := by
  have e : ((typeFrame ϖ o).bas⁻¹).val =
      fromBlocks 1 0 0 (diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    change fromBlocks 1 0 0 (diagonal _) * _ = _
    simp [fromBlocks_multiply, diagonal_mul_diagonal]
  have e' : (typeFrame ϖ o').bas.val =
      fromBlocks 1 0 0 (diagonal fun i : Fin c' => (ϖ : k) ^ (i.val + 1)) := rfl
  unfold LatFrame.coords
  rw [e, e', ← diagonal_one, ← diagonal_one, fromBlocks_diagonal, fromBlocks_diagonal, submatrix_apply,
    mul_diagonal, diagonal_mul]
  rfl

theorem coords_add (F : LatFrame k ι (n ⊕ Fin c)) (F' : LatFrame k ι' (n' ⊕ Fin c'))
    (x y : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) :
    F.coords F' (x + y) = F.coords F' x + F.coords F' y := by
  unfold LatFrame.coords
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl

end SlopeTestRemainingChoices

theorem phi_add_col (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (hP : S.Pattern t)
    (j c : ℕ) (H : j + c = s) (q : Fin c) (hρ : q.val + 1 ≤ S.ρ) (hc : q.val + 2 ≤ c)
    (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k)
    (hx : ∀ r, x (Sum.inl r) (Sum.inr q.succ) = 0) (w : XIx (Fin κ) t (j + 1) → k) :
    (S.T t).Phi j c H (x + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0) =
      if ∀ r, valuation k (((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r) < 1 then (S.T t).Phi j c H x else 0 := by
  have H1 : j + 1 + c = s + 1 := by omega
  have H2 : j + (c + 1) = s + 1 := by omega
  have hPhi : ∀ z, (S.T t).Phi j c H z = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ (stdOrd (Fin κ) t (j + 1) c H1)).coords
        (typeFrame S.ϖ (stdOrd (Fin κ) t j (c + 1) H2)) z).submatrix (ixSucc _ t j) id) := fun _ => rfl
  split_ifs with hw
  · rw [hPhi, hPhi, coords_add, Matrix.submatrix_add, Pi.add_apply, Pi.add_apply]
    refine (S.P.iter t S.μ S.tame j).Phi_add (S.tame _) _ fun a b => ?_
    rw [submatrix_apply, coords_typeFrame_apply, of_apply]
    split_ifs with hb
    · rw [hb]
      rcases stdOrd (Fin κ) t (j + 1) c H1 (ixSucc _ t j a) with r | r
      · simpa [mul_comm] using hw r
      · simp
    · simp
  · by_contra h
    rw [← Ne, hPhi, TypeDatum.Phi_ne_zero_iff] at h
    obtain ⟨⟨g, hg, e⟩, hb⟩ := h
    refine hw fun r => ?_
    obtain ⟨a, ha⟩ := ((ixSucc _ t j).trans (stdOrd (Fin κ) t (j + 1) c H1)).surjective (.inl r)
    simp only [Equiv.trans_apply] at ha
    have hq : q.succ.val < s + 1 := by have := q.succ.2; omega
    have hcol : stdOrd (Fin κ) t j (c + 1) H2 (.inl (.inr ⟨q.succ.val, hq⟩)) = .inr q.succ :=
      standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1) H2 q.succ
    have key : (((typeFrame S.ϖ (stdOrd (Fin κ) t (j + 1) c H1)).coords
        (typeFrame S.ϖ (stdOrd (Fin κ) t j (c + 1) H2))
        (x + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0)).submatrix (ixSucc _ t j) id)
        a (.inl (.inr ⟨q.succ.val, hq⟩)) = ((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r := by
      rw [submatrix_apply, coords_typeFrame_apply, id, ha, hcol]
      simp [hx, mul_comm]
    rw [← key]
    rcases a with a | a
    · have hne : ¬ FreeIx S.ρ a (.inl (.inr ⟨q.succ.val, hq⟩)) ∧ a ≠ .inl (.inr ⟨q.succ.val, hq⟩) := by
        rcases a with (a | a) | a
        · simp only [FreeIx, FreeTop, Fin.val_succ]
          exact ⟨by omega, by simp⟩
        · have hac : c ≤ a.val := by
            by_contra hlt
            have := standardOrderExtendedBasis_apply_low_block (Fin κ) t (j + 1) c H1 ⟨a.val, by omega⟩
            exact Sum.inr_ne_inl (this.symm.trans ha)
          simp only [FreeIx, FreeTop, Fin.lt_def, Fin.val_succ, ne_eq, Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff]
          omega
        · simp [FreeIx]
      have := ((hP j g).1 hg).2 a _ hne.1
      rw [e, Matrix.one_apply_ne hne.2, sub_zero] at this
      exact this
    · exact hb a _

end GlobalTheory.SymChain.ExchangeCol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialFourierInversion
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open scoped Topology

noncomputable section
namespace GlobalTheory.LocFlat.PartialFourier

theorem eventually_add_invariant {X : Type*} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
    {f : X → ℂ} (hf : f ∈ SB X) : ∀ᶠ t in 𝓝 (0 : X), ∀ x, f (x + t) = f x := by
  have h1 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : X × X => (f (q.2 + q.1), f q.2) :=
      (hf.1.comp_continuous (by fun_prop)).prodMk (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  have h1' : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + -t) = f x :=
    (continuous_neg.tendsto' (0 : X) 0 neg_zero).eventually h1
  filter_upwards [h1, h1'] with t ht ht' x
  by_cases hx : x ∈ tsupport f
  · exact ht x hx
  by_cases hx' : x + t ∈ tsupport f
  · have := ht' _ hx'
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]


omit [BorelSpace k] in
theorem partial_mem_SB {I J : Type} [Fintype I] [Fintype J] (ν : Measure k) {f : (I → k) × (J → k) → ℂ}
    (hf : f ∈ SB ((I → k) × (J → k))) :
    (fun x₁ : I → k => ∫ y : J → k, f (x₁, y) ∂(Measure.pi fun _ => ν)) ∈ SB (I → k) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_, ?_⟩
  · have h2 : Filter.Tendsto (fun z : I → k => ((z - x, 0) : (I → k) × (J → k))) (𝓝 x) (𝓝 0) := by
      have : Continuous (fun z : I → k => ((z - x, 0) : (I → k) × (J → k))) := by fun_prop
      convert this.tendsto x using 2
      simp only [sub_self]
      rfl
    filter_upwards [h2.eventually (eventually_add_invariant hf)] with z hz
    congr 1
    funext y
    have := hz (x, y)
    simpa using this
  · refine HasCompactSupport.intro (hf.2.image continuous_fst) fun x hx => ?_
    have : ∀ y, f (x, y) = 0 := fun y => image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩
    simp [this]

theorem partial_fourier_inversion : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (I : Type) [Fintype I], ∃ C : ℝ, 0 < C ∧ ∀ (J : Type) [Fintype J] (a : I → k), ∀ f ∈ SB ((I → k) × (J → k)), Integrable (fun l : I → k => ∫ x : (I → k) × (J → k), f x * (ψ (l ⬝ᵥ x.1) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν))) (Measure.pi fun _ => ν) ∧ ∫ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * (∫ x : (I → k) × (J → k), f x * (ψ (l ⬝ᵥ x.1) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν))) ∂(Measure.pi fun _ => ν) = (C : ℂ) * ∫ y : J → k, f (a, y) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ ψ ν hψ hne hν I _
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ hne
  have hO : 0 < ν.real (𝒪[k] : Set k) :=
    ENNReal.toReal_pos ((isOpen_int k).measure_pos ν ⟨0, zero_mem _⟩).ne' (isCompact_int k).measure_lt_top.ne
  have hpsi : ∀ u : k, (ψ (-u) : ℂ) * ψ u = 1 := by
    intro u
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
  refine ⟨(nabs k c * ν.real (𝒪[k] : Set k) ^ 2) ^ Fintype.card I, by have := nabs_pos k c; positivity,
    fun J _ a f hf => ?_⟩
  set μI : Measure (I → k) := Measure.pi fun _ => ν with hμI
  set μJ : Measure (J → k) := Measure.pi fun _ => ν with hμJ
  set g : (I → k) → ℂ := fun x₁ => ∫ y, f (x₁, y) ∂μJ with hgdef
  have hg : g ∈ SB (I → k) := partial_mem_SB ν hf
  have hF : ∀ l : I → k, ∫ x, f x * (ψ (l ⬝ᵥ x.1) : ℂ) ∂(μI.prod μJ) = ∫ x₁, g x₁ * (ψ (x₁ ⬝ᵥ l) : ℂ) ∂μI := by
    intro l
    have hfi : Integrable f (μI.prod μJ) := hf.1.continuous.integrable_of_hasCompactSupport hf.2
    have hi : Integrable (fun x => f x * (ψ (l ⬝ᵥ x.1) : ℂ)) (μI.prod μJ) :=
      hfi.mul_bdd (c := 1)
        ((continuous_subtype_val.comp (hψ.comp (continuous_const.dotProduct continuous_fst))).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun q => (Circle.norm_coe _).le)
    rw [integral_prod _ hi]
    congr 1
    funext x
    simp only
    rw [integral_mul_const, dotProduct_comm l x]
  simp only [hF]
  refine ⟨?_, ?_⟩
  · have := FourierPi.fourier_mem_SB μI hc hg
    exact this.1.continuous.integrable_of_hasCompactSupport this.2
  · set h : (I → k) → ℂ := fun x => g (x + a) with hhdef
    have hh : h ∈ SB (I → k) :=
      ⟨hg.1.comp_continuous (continuous_add_const a), hg.2.comp_homeomorph (Homeomorph.addRight a)⟩
    have htr : ∀ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * ∫ x₁, g x₁ * (ψ (x₁ ⬝ᵥ l) : ℂ) ∂μI =
        ∫ x, h x * (ψ (x ⬝ᵥ l) : ℂ) ∂μI := by
      intro l
      rw [← integral_const_mul, ← integral_add_right_eq_self _ a]
      congr 1
      funext x
      have e1 : (x + a) ⬝ᵥ l = x ⬝ᵥ l + l ⬝ᵥ a := by rw [add_dotProduct, dotProduct_comm a l]
      rw [hhdef, e1, AddChar.map_add_eq_mul, Circle.coe_mul]
      linear_combination (g (x + a) * (ψ (x ⬝ᵥ l) : ℂ)) * hpsi (l ⬝ᵥ a)
    simp only [htr]
    obtain ⟨s, hs⟩ := FourierPi.fourier_inversion_pi μI hc hh
    have hb : ∀ r : kˣ, μI.real (FourierPi.box I r) = ν.real (cball r) ^ Fintype.card I := by
      intro r
      simp [hμI, Measure.real, FourierPi.box, Measure.pi_pi]
    rw [hs, hb, hb, ← mul_pow, measureReal_cball, measureReal_cball]
    have h4 : nabs k c = nabs k s * nabs k (c * s⁻¹) := by
      rw [← nabs_mul, mul_comm, inv_mul_cancel_right]
    simp only [hhdef, zero_add, hgdef, h4]
    push_cast
    ring

end GlobalTheory.LocFlat.PartialFourier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalOverDiagonalDoubleCosetRepsStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_borelSpherical_over_diagonalDoubleCosetReps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → (∀ i, γ i ≠ 0) → ∀ (s : Finset (Fin N)) (R : Finset (GL (Fin N) k)), IsRepsK (GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (indic s)) R → ∑ g ∈ R, ψ g = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s.card, ((resCard k : ℂ) ^ ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card * ∏ a ∈ S, γ a) := by
  first | exact @GlobalTheory.BorelCosetSum.sum_cosets_eq | exact GlobalTheory.BorelCosetSum.sum_cosets_eq | (intros; apply GlobalTheory.BorelCosetSum.sum_cosets_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainOneLatticeClassStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricChain_oneLatticeClass : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneClass t ν := by
  first | exact @GlobalTheory.SymChain.LatClass.oneClass_symChain | exact GlobalTheory.SymChain.LatClass.oneClass_symChain | (intros; apply GlobalTheory.SymChain.LatClass.oneClass_symChain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainProjectedLevelOfPatternStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricChain_projected_level_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.PrLevel t := by
  first | exact @GlobalTheory.SymChain.PrImage.prLevel_of_pattern | exact GlobalTheory.SymChain.PrImage.prLevel_of_pattern | (intros; apply GlobalTheory.SymChain.PrImage.prLevel_of_pattern <;> assumption)
end

