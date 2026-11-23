module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0108
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0094
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0101
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0102
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0103
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0106
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeZigzagCompat
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZig

universe w

variable {R : Type} [CommRing R]

def shift {K : DCx.{w} R} (B : ∀ p q, K.X p q →ₗ[R] K.X (p + 1) (q + 1)) (x : ∀ p q, K.X p q) : ∀ p q, K.X p q
  | 0, _ => 0
  | _ + 1, 0 => 0
  | p + 1, q + 1 => (-1 : ℤ) ^ q • B p q (x p q)

variable {K : DCx.{w} R} (B : ∀ p q, K.X p q →ₗ[R] K.X (p + 1) (q + 1))

theorem shift_sub (x y : ∀ p q, K.X p q) : shift B (x - y) = shift B x - shift B y := by
  funext p q
  rcases p with _ | p <;> rcases q with _ | q <;> simp [shift, smul_sub]

theorem shift_sgl (p q : ℕ) (x : K.X p q) :
    shift B (K.sgl p q x) = (-1 : ℤ) ^ q • K.sgl (p + 1) (q + 1) (B p q x) := by
  funext a b
  rcases a with _ | a
  · rw [Pi.smul_apply, Pi.smul_apply, K.sgl_ne _ (Or.inl (by omega))]
    simp [shift]
  · rcases b with _ | b
    · rw [Pi.smul_apply, Pi.smul_apply, K.sgl_ne _ (Or.inr (by omega))]
      simp [shift]
    · by_cases h : a = p ∧ b = q
      · obtain ⟨rfl, rfl⟩ := h
        simp only [shift, Pi.smul_apply, K.sgl_self]
      · rw [Pi.smul_apply, Pi.smul_apply, K.sgl_ne _ (by omega)]
        simp only [shift]
        rw [K.sgl_ne _ (by omega)]
        simp

theorem D_shift (hh : ∀ p q x, K.dh (p + 1) (q + 1) (B p q x) = B (p + 1) q (K.dh p q x))
    (hv : ∀ p q x, K.dv (p + 1) (q + 1) (B p q x) = B p (q + 1) (K.dv p q x)) (x : ∀ p q, K.X p q) :
    K.D (shift B x) = shift B (K.D x) := by
  funext p q
  rw [K.D_apply]
  rcases p with _ | p
  · rcases q with _ | q <;> simp [DCx.Dh, DCx.Dv, shift]
  · rcases q with _ | q
    · rcases p with _ | p <;> simp [DCx.Dh, DCx.Dv, shift]
    · have h1 : K.Dh (shift B x) (p + 1) (q + 1) = (-1 : ℤ) ^ q • B p q (K.Dh x p q) := by
        rcases p with _ | p
        · simp [DCx.Dh, shift]
        · simp [DCx.Dh, shift, hh]
      have h2 : K.Dv (shift B x) (p + 1) (q + 1) = (-1 : ℤ) ^ (q + 1) • B p q (K.Dv x p q) := by
        rcases q with _ | q
        · simp [DCx.Dv, shift]
        · simp only [DCx.Dv, shift, map_zsmul, hv]
          rw [pow_succ, pow_succ]
          simp
      rw [h1, h2]
      show _ = (-1 : ℤ) ^ q • B p q (K.D x p q)
      rw [K.D_apply, map_add (f := _), map_zsmul, smul_add, smul_smul, smul_smul, pow_succ, pow_succ]
      congr 2
      ring

theorem cone_zigzag_compat (hh : ∀ p q x, K.dh (p + 1) (q + 1) (B p q x) = B (p + 1) q (K.dh p q x))
    (hv : ∀ p q x, K.dv (p + 1) (q + 1) (B p q x) = B p (q + 1) (K.dv p q x))
    (a : ∀ k, K.X 0 (2 * k)) (g : ∀ k, K.X 0 (2 * k + 1)) (P : ∀ k, K.X k k)
    (hg1 : ∀ k, K.dv 0 (2 * k + 1) (g k) = a (k + 1))
    (hg2 : ∀ k, K.dh 0 (2 * k + 1) (g k) = - B 0 (2 * k) (a k))
    (hP0 : P 0 = a 0) (hPs : ∀ k, P (k + 1) = (-1 : ℤ) ^ k • B k k (P k)) (k : ℕ) :
    ∃ U : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ 2 * k → U p q = 0) ∧
      K.D U = K.sgl 0 (2 * k) (a k) - K.sgl k k (P k) := by
  induction k with
  | zero =>
    refine ⟨0, fun _ _ _ => rfl, ?_⟩
    rw [map_zero, hP0]
    exact (sub_self _).symm
  | succ k ih =>
    obtain ⟨U, hU, hDU⟩ := ih
    refine ⟨shift B U + K.sgl 0 (2 * k + 1) (g k), fun p q h => ?_, ?_⟩
    · rw [Pi.add_apply, Pi.add_apply, K.sgl_ne _ (by omega), add_zero]
      rcases p with _ | p
      · rfl
      · rcases q with _ | q
        · rfl
        · simp only [shift]
          rw [hU p q (by omega)]
          simp
    · rw [map_add (f := _), D_shift B hh hv, hDU, shift_sub, shift_sgl, shift_sgl, K.D_sgl, hg1, hg2, hPs, map_neg, map_zsmul]
      have e : ((-1 : ℤ) ^ (2 * k)) = 1 := by rw [pow_mul]; simp
      rw [e, one_smul, pow_zero, one_smul]
      have e2 : K.sgl 0 (2 * k + 1 + 1) (a (k + 1)) = K.sgl 0 (2 * (k + 1)) (a (k + 1)) := rfl
      rw [e2]
      abel

theorem zig_stair (F : GlobalTheory.CompanionTheory.ConeCech.DFil K) (n : ℕ) (hTop : ∀ p q, F.L 0 p q = ⊤)
    (hV : ∀ p q, n + 1 < p → Subsingleton (K.X p q)) (hE : ∀ (r : ℕ) p q, q ≠ r → F.Ex (r : ℤ) p q)
    (hh : ∀ p q x, K.dh (p + 1) (q + 1) (B p q x) = B (p + 1) q (K.dh p q x))
    (hv : ∀ p q x, K.dv (p + 1) (q + 1) (B p q x) = B p (q + 1) (K.dv p q x))
    (a : ∀ k, K.X 0 (2 * k)) (g : ∀ k, K.X 0 (2 * k + 1)) (P : ∀ k, K.X k k)
    (hg1 : ∀ k, K.dv 0 (2 * k + 1) (g k) = a (k + 1))
    (hg2 : ∀ k, K.dh 0 (2 * k + 1) (g k) = - B 0 (2 * k) (a k))
    (hP0 : P 0 = a 0) (hPs : ∀ k, P (k + 1) = (-1 : ℤ) ^ k • B k k (P k))
    (hP : P (n + 1) ∈ F.L ((n : ℤ) + 1) (n + 1) (n + 1))
    (v : K.X 0 (2 * n + 1)) (hv1 : K.dv 0 (2 * n + 1) v = a (n + 1)) (hv2 : K.dh 0 (2 * n + 1) v = 0) :
    ∃ (ω : K.X n (n + 1)) (f : K.X (n + 1) n), ω ∈ F.L ((n : ℤ) + 1) n (n + 1) ∧
      K.dv n (n + 1) ω ∈ F.L ((n : ℤ) + 1 + 1) n (n + 2) ∧ f ∈ F.L (n : ℤ) (n + 1) n ∧
      P (n + 1) = K.dh n (n + 1) ω + (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n f := by
  obtain ⟨U, hU, hDU⟩ := cone_zigzag_compat B hh hv a g P hg1 hg2 hP0 hPs (n + 1)
  refine GlobalTheory.CompanionTheory.ConeCech.stair F n hTop hV hE (P (n + 1)) hP (K.sgl 0 (2 * n + 1) v - U) ?_ ?_
  · refine sub_mem (fun p q h => K.sgl_ne _ (by omega)) (fun p q h => hU p q (by omega))
  · rw [map_sub, hDU, K.D_sgl, hv1, hv2, map_zero, zero_add, pow_zero, one_smul]
    have e2 : K.sgl 0 (2 * n + 1 + 1) (a (n + 1)) = K.sgl 0 (2 * (n + 1)) (a (n + 1)) := rfl
    rw [e2]
    abel

end GlobalTheory.CompanionTheory.ConeZig
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalWhittaker
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep

theorem colGeR_single (K : Type) [Field K] (d j : ℕ) (hj : 1 ≤ j) :
    colGeR K d j (Pi.single (⟨j - 1, by omega⟩ : Fin j) (1 : K) : Fin j → K) = colGeE K d j := by
  funext i l
  by_cases hl : (l : ℕ) = j
  · by_cases hi : (l : ℕ) = i + 1
    · have hlt : (i : ℕ) < j := by omega
      have hij : (⟨(i : ℕ), hlt⟩ : Fin j) = ⟨j - 1, by omega⟩ := Fin.ext (by simp; omega)
      simp only [colGeR, colGeE]
      rw [dite_eq_left ⟨hl, hlt⟩, hij]
      simp [hl, hi]
      omega
    · simp only [colGeR, colGeE]
      by_cases hlt : (i : ℕ) < j
      · rw [dite_eq_left ⟨hl, hlt⟩]
        have hne : (⟨(i : ℕ), hlt⟩ : Fin j) ≠ ⟨j - 1, by omega⟩ := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        simp [hi, Pi.single_eq_of_ne hne]
      · rw [dite_eq_right (by tauto)]
        simp [hi]
  · simp only [colGeR, colGeE]
    rw [dite_eq_right (by tauto)]
    have : (j + 1 ≤ (l : ℕ)) ↔ j ≤ (l : ℕ) := by omega
    simp [this]

theorem wh_row_ne_zero (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ)
    (χ : GL (Fin d) K → ℂ) (hj : 1 ≤ j) (hd : j < d) (hχ : ∀ x y, χ (x * y * x⁻¹) = χ y)
    (r : Fin j → K) (hr : r ≠ 0) :
    wh (colGe d j) (colGeR K d j r) ψ₀ χ = wh (colGe d j) (colGeE K d j) ψ₀ χ := by
  have hs : (Pi.single (⟨j - 1, by omega⟩ : Fin j) (1 : K) : Fin j → K) ≠ 0 := by
    intro h
    have := congrFun h ⟨j - 1, by omega⟩
    simp at this
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows K j r _ hr hs
  obtain ⟨h, h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb K d j hd.le g
  rw [_root_.GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.wh_colGeR_conj K d j ψ₀ χ g h r hd hχ h1 h2, hg, colGeR_single K d j hj]

theorem wh_step (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) (hψ : ψ₀ ≠ 1) (hτ : IsCuspidal K τ) (hj : 1 ≤ j) (hd : j < d) :
    wh (colGe d (j + 1)) (colGeE K d (j + 1)) ψ₀ τ.character =
      ((Fintype.card K : ℂ) ^ j - 1) * wh (colGe d j) (colGeE K d j) ψ₀ τ.character := by
  rw [GlobalTheory.T.whittaker_column_recursion K d j ψ₀ τ.character hd (GlobalTheory.T.pattern_set_card_column_step K d j hd) (_root_.GlobalTheory.CompanionTheory.TyFin.Orth.orth K j ψ₀ hψ)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin j → K)),
    GlobalTheory.T.whittaker_vanishes_of_radical_sums K d j ψ₀ τ.character (_root_.GlobalTheory.CompanionTheory.TyFin.CuspSum.sum_character_translate K d j τ hj hd hτ), zero_add,
    Finset.sum_congr rfl (fun r hr => wh_row_ne_zero K d j ψ₀ τ.character hj hd
      (fun x y => FDRep.char_conj τ y x) r (Finset.ne_of_mem_erase hr))]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  have h1 : 1 ≤ Fintype.card K ^ j := Nat.one_le_pow _ _ Fintype.card_pos
  rw [Nat.cast_sub h1]
  simp

theorem wh_top (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) :
    wh (colGe d d) (colGeE K d d) ψ₀ τ.character = (Module.finrank ℂ τ : ℂ) := by
  classical
  have hset : patSet K (colGe d d) = {1} := by
    ext u
    simp only [patSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      ext i l
      by_cases hil : i = l
      · subst hil; simpa using (h i i).1 rfl
      · have := (h i l).2 hil (fun hc => by have := hc.2; have := l.2; omega)
        simp [this, Matrix.one_apply_ne hil]
    · rintro rfl i l
      exact ⟨fun h => by simp [h], fun h _ => by simp [Matrix.one_apply_ne h]⟩
  have hE : patChar (colGeE K d d) ψ₀ (1 : GL (Fin d) K) = 1 := by
    have : ∀ i l : Fin d, colGeE K d d i l = 0 := by
      intro i l
      simp only [colGeE]
      rw [if_neg]
      rintro ⟨-, h⟩
      have := l.2
      omega
    simp [patChar, this]
  simp only [wh, hset, Set.ncard_singleton, Set.mem_singleton_iff]
  simp [hE, FDRep.char_one]

theorem wh_one_eq (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) :
    wh (colGe d 1) (colGeE K d 1) ψ₀ χ = wh (fun i j : Fin d => i < j) (cutE K d 0) ψ₀ χ := by
  have h1 : colGe d 1 = fun i j : Fin d => i < j := by
    funext i l
    simp only [colGe, eq_iff_iff, and_iff_left_iff_imp]
    intro h
    have : (i : ℕ) < l := h
    omega
  have h2 : colGeE K d 1 = cutE K d 0 := by
    funext i l
    simp only [colGeE, cutE]
    congr 1
    apply propext
    omega
  rw [h1, h2]

theorem wh_prod (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) (hψ : ψ₀ ≠ 1) (hτ : IsCuspidal K τ) (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    wh (colGe d k) (colGeE K d k) ψ₀ τ.character =
      wh (colGe d 1) (colGeE K d 1) ψ₀ τ.character * ∏ i ∈ Finset.Ico 1 k, ((Fintype.card K : ℂ) ^ i - 1) := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [wh_step K d k ψ₀ τ hψ hτ hk (by omega), ih (by omega), Finset.prod_Ico_succ_top hk]
    ring

theorem cuspWh : ReciprocityTheory.Ty.Fin.St.CuspWh := by
  intro K _ _ _ d ψ₀ τ hψ hτ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [← wh_top K 0 ψ₀ τ]
    have h1 : colGe 0 0 = fun i j : Fin 0 => i < j := by
      funext i; exact i.elim0
    have h2 : colGeE K 0 0 = cutE K 0 0 := by
      funext i; exact i.elim0
    rw [h1, h2]
    simp
  · rw [← wh_top K d ψ₀ τ, wh_prod K d ψ₀ τ hψ hτ d hd le_rfl, wh_one_eq]

end GlobalTheory.CompanionTheory.TyFin.ColStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeUnique
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtSpecProof

section Sections

variable {R : Type} [CommRing R]

theorem res_comp {G : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec G U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun m => m.hom x) h

end Sections

variable {q : ℕ} {C : Type 1} [Category.{0} C] {P : Probe C q} {X : Scheme.{0}}

theorem map_glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X)
    {c c' : C} (φ : c ⟶ c') :
    (((P.res i).K j).map φ).hom (Sec.res (Y.y c) a) = Sec.res (Y.y c') a := by
  change Sec.res (P.S.map φ).unop (Sec.res (Y.y c) a) = _
  rw [← res_comp, Y.nat]

theorem d_glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    d ((P.res i).K j) 0 (Y.glob i j a) = 0 := by
  funext s
  have h : ∀ k : Fin 2, (((P.res i).K j).map (GlobalTheory.CatH.toLast k s)).hom (Y.glob i j a (GlobalTheory.CatH.face k s)) =
      Sec.res (Y.y (s.obj (Fin.last 1))) a := fun k => map_glob Y i j a _
  change ∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) •
    (((P.res i).K j).map (GlobalTheory.CatH.toLast k s)).hom (Y.glob i j a (GlobalTheory.CatH.face k s)) = 0
  rw [Fin.sum_univ_two, h 0, h 1]
  simp

theorem dvC_glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    (P.res i).dvC j 0 (Y.glob i j a) =
      Y.glob i (j + 1) (Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (j : ℤ) ((j + 1 : ℕ) : ℤ)) a) := by
  funext s
  exact map_res _ _ _

theorem glob_add (Y : P.Pts X) (i : ℤ) (j : ℕ) (a b : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    Y.glob i j (a + b) = Y.glob i j a + Y.glob i j b := by
  funext s
  exact map_add _ _ _

theorem glob_sub (Y : P.Pts X) (i : ℤ) (j : ℕ) (a b : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    Y.glob i j (a - b) = Y.glob i j a - Y.glob i j b := by
  funext s
  exact map_sub _ _ _

theorem edge_exists {i : ℤ} {j : ℕ} (hT : (P.res i).Good) (hSE : StEx) (hRB : RepBasic) (Y : P.Pts X)
    {x : Ht q (sch.obj X) j i} {a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X} (hx : Rep x a) :
    ∃ h, (P.res i).Edge (Y.glob i j a) h := by
  have hcl := (hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).2.1 x a hx ((j + 1 : ℕ) : ℤ)
  have hdv : (P.res i).dvC j 0 (Y.glob i j a) = 0 := by
    rw [dvC_glob, hcl]
    funext s
    exact map_zero _
  obtain ⟨z, hz, hst⟩ := hSE ℤ C P.L (P.res i) hT j 0 j (add_zero j) (Y.glob i j a) hdv (d_glob Y i j a)
  exact ⟨(cx P.L).cls z hz, z, hz, hst, rfl⟩

theorem edge_unique {i : ℤ} {j : ℕ} (hT : (P.res i).Good) (hEU : EdgeUniq) (hRB : RepBasic) (hRZ : ResZero)
    (Y : P.Pts X) {x : Ht q (sch.obj X) j i} {a a' : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X}
    (hx : Rep x a) (hx' : Rep x a') {h h' : H P.L j} (he : (P.res i).Edge (Y.glob i j a) h)
    (he' : (P.res i).Edge (Y.glob i j a') h') : h = h' := by
  have hB := hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)
  have h0 : Rep (0 : Ht q (sch.obj X) j i) (a - a') := by
    have := (hB.2.2.1 x x a a' hx hx').2
    rwa [sub_self] at this
  have hz := hB.2.2.2.1 (a - a') h0
  have hVB : (P.res i).VB j (Y.glob i j a - Y.glob i j a') := by
    cases j with
    | zero =>
      obtain ⟨b, hb⟩ := hz (-1) (by norm_num)
      have := (hRZ (ZMod q) (tw q i) X).2.2 (-1) (by norm_num)
      have hb0 : b = 0 := Subsingleton.elim _ _
      have hz0 : a - a' = 0 := by
        rw [← hb, hb0]
        exact map_zero _
      change Y.glob i 0 a - Y.glob i 0 a' = 0
      rw [← glob_sub, hz0]
      funext s
      exact map_zero _
    | succ s =>
      obtain ⟨b, hb⟩ := hz (s : ℤ) (by push_cast; rfl)
      refine ⟨Y.glob i s b, d_glob Y i s b, ?_⟩
      rw [dvC_glob, hb, glob_sub]
  exact (hEU ℤ C P.L (P.res i) hT j _ _ h h' he he').2 hVB

theorem etSpec : ResGood → StEx → EdgeUniq → RepBasic → ResZero → EtSpec := by
  intro hRG hSE hEU hRB hRZ hGen q _ C _ P X Y i j x
  have hT := hRG hGen q C P i
  have hB := hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)
  have hex : ∀ x, ∃ h, Y.IsEt i j x h := fun x => by
    obtain ⟨a, ha⟩ := hB.1 x
    obtain ⟨h, hh⟩ := edge_exists hT hSE hRB Y ha
    exact ⟨h, a, ha, hh⟩
  have huniq : ∀ {x h h'}, Y.IsEt i j x h → Y.IsEt i j x h' → h = h' := by
    rintro x h h' ⟨a, ha, he⟩ ⟨a', ha', he'⟩
    exact edge_unique hT hEU hRB hRZ Y ha ha' he he'
  have hall : ∀ x, Y.IsEt i j x (Y.et i j x) := by
    refine pick_spec (P := fun e : Ht q (sch.obj X) j i →+ H P.L j => ∀ x, Y.IsEt i j x (e x)) ?_
    choose f hf using hex
    refine ⟨AddMonoidHom.mk' f fun u v => huniq (hf _) ?_, hf⟩
    obtain ⟨a, ha, he⟩ := hf u
    obtain ⟨b, hb, he'⟩ := hf v
    refine ⟨a + b, (hB.2.2.1 u v a b ha hb).1, ?_⟩
    rw [glob_add]
    exact (hEU ℤ C P.L (P.res i) hT j _ _ _ _ he he').1
  refine ⟨fun a ha => ?_, fun h hh => huniq hh (hall x)⟩
  obtain ⟨h, hh⟩ := edge_exists hT hSE hRB Y ha
  have e : h = Y.et i j x := huniq ⟨a, ha, hh⟩ (hall x)
  rwa [← e]

end GlobalTheory.CompanionTheory.EtSpecProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

section Abstract

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V]

def twRel (ρ : Representation ℂ Γ V) (ψ : Γ →* ℂˣ) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ (γ : Γ) (v : V), w = ρ γ v - (ψ γ : ℂ) • v}

end Abstract

section Fibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

def fibChar (μ : kˣ →* ℂˣ) : GL a k × (GL c k × GL d k) →* ℂˣ :=
  (detChar a (μ⁻¹ * absPow k (((Fintype.card c : ℂ) + Fintype.card d) / 2))).comp (MonoidHom.fst _ _) *
    (detChar c (μ * absPow k (-(Fintype.card a : ℂ) / 2) * absPow k (-(Fintype.card d : ℂ) / 2))).comp
      ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)) *
    (detChar d (μ * absPow k (-(Fintype.card a : ℂ) / 2) * absPow k ((Fintype.card c : ℂ) / 2))).comp
      ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _))

def fibBase (κ : ℕ) :
    Representation ℂ (GL a k × GL c k) (SB (RankIn (k := k) (a := a) (b := c) {κ})) :=
  sbRep (fun x γ => ⟨act x.1 γ, by rw [rank_act]; exact x.2⟩)
    (fun x => Subtype.ext (act_one x.1)) (fun x γ δ => Subtype.ext (act_mul x.1 γ δ))
    (fun γ => ((continuous_act γ).comp continuous_subtype_val).subtype_mk _)

def fibRep (μ : kˣ →* ℂˣ) (κ : ℕ) :
    Representation ℂ (GL a k × (GL c k × GL d k)) (SB (RankIn (k := k) (a := a) (b := c) {κ})) :=
  twist ((fibBase a c κ).comp ((MonoidHom.id _).prodMap (MonoidHom.fst _ _))) (fibChar a c d μ)

theorem fibRep_apply (μ : kˣ →* ℂˣ) (κ : ℕ) (g : GL a k) (p₁ : GL c k) (p₂ : GL d k)
    (φ : SB (RankIn (k := k) (a := a) (b := c) {κ})) (y : RankIn (k := k) (a := a) (b := c) {κ}) :
    (fibRep a c d μ κ (g, p₁, p₂) φ).1 y = (fibChar a c d μ (g, p₁, p₂) : ℂ) *
      φ.1 ⟨act y.1 (g, p₁), by rw [rank_act]; exact y.2⟩ := rfl

def rightRep (κ : ℕ) :
    Representation ℂ (GL a k) (SB (RankIn (k := k) (a := a) (b := c) {κ})) :=
  (fibBase a c κ).comp (MonoidHom.inl _ _)

end Fibre

end GlobalTheory.CompanionTheory.ThetaGLLen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedRootOfRep
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem redRoot_of_rep : CrystallineSemistableComparison.E.RepRoot → CrystallineSemistableComparison.E.RepOp → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.RedRoot := by
  intro hRoot hOp hConc inOp inRed Q q _ _ hq i X ζ ξ hξ
  have h1 : Rep (rootClass i ζ) (resGen i ζ) := (hRoot Q i X ζ).2
  have h2 : Rep (rootClass i ξ) (resGen i ξ) := (hRoot q i X ξ).2
  have h3 := hOp inOp _ _ _ _ (redMap Q q i) X 0 (rootClass i ζ) _ h1
  rw [inRed Q q hq i X ζ ξ hξ] at h3
  exact (hConc (ZMod q) _ X 0 (resGen i ξ)).2.2 _ _ h3 h2

end GlobalTheory.CompanionTheory.EdgeMap
end

