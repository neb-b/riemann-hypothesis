module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0019
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0014
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0020
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0017

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieMemCInv
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Atom

variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]

theorem rowShift_C (σ : T) (i i' : Fin (r σ)) (t z : C) :
    rowShift r n C σ i i' t (MvPolynomial.C z) = MvPolynomial.C z := (rowShift r n C σ i i' t).commutes z

variable {N N' : ℕ} (Φ : MvPolynomial (Fin N × Fin N') C →ₐ[C] MvPolynomial (Letter T r n) C) (σ0 : T)
  (w : Fin N → Fin 2 → C) (lt : Fin N × Fin N' → Fin 2 → Letter T r n) (colf : Fin N → Fin 2 → Fin n)

theorem shift_same (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (σ : T) (i i' : Fin (r σ)) (t : C)
    (ρ : Fin N) (c : Fin N') (h : ¬ (σ = σ0 ∧ c.val = i.val)) :
    rowShift r n C σ i i' t (Φ (X (ρ, c))) = Φ (X (ρ, c)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hΦ, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, rowShift_C, rowShift_X, hlt, if_neg]
  intro e
  apply h
  exact ⟨(congrArg (fun x : T × ℕ × Fin n => x.1) e).symm, congrArg (fun x : T × ℕ × Fin n => x.2.1) e⟩

theorem shift_add (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (i i' : Fin (r σ0)) (t : C)
    (ρ : Fin N) (c c' : Fin N') (hc : c.val = i.val) (hc' : c'.val = i'.val) :
    rowShift r n C σ0 i i' t (Φ (X (ρ, c))) = Φ (X (ρ, c)) + MvPolynomial.C t * Φ (X (ρ, c')) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hΦ, hΦ, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h2 : (lt (ρ, c) q).2.2 = colf ρ q := congrArg (fun x : T × ℕ × Fin n => x.2.2) (hlt ρ c q)
  have h1 : keyL (lt (ρ, c) q) = (σ0, i.val, (lt (ρ, c) q).2.2) := by rw [hlt, hc, h2]
  rw [map_mul, rowShift_C, rowShift_X, if_pos h1]
  have h3 : (⟨σ0, i', (lt (ρ, c) q).2.2⟩ : Letter T r n) = lt (ρ, c') q := by
    apply keyL_inj
    rw [hlt, hc', h2]
    rfl
  rw [h3]
  ring

theorem rowShift_minor_lin (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) (k : ℕ) :
    rowShift r n C σ i i' t (Φ (minorK C N N' k)) = Φ (minorK C N N' k) := by
  unfold minorK
  split_ifs with h
  · set A : Matrix (Fin k) (Fin k) (MvPolynomial (Letter T r n) C) :=
      Matrix.of fun b c => Φ (X (Fin.castLE h.1 b, Fin.castLE h.2 c)) with hA
    have e1 : Φ (Matrix.of fun b c : Fin k =>
        (X (Fin.castLE h.1 b, Fin.castLE h.2 c) : MvPolynomial (Fin N × Fin N') C)).det = A.det := by
      rw [AlgHom.map_det]
      congr 1
    rw [e1, AlgHom.map_det]
    by_cases hc : σ = σ0 ∧ i.val < k
    · obtain ⟨rfl, hik⟩ := hc
      have hi' : i'.val < i.val := hi
      let ci : Fin k := ⟨i.val, hik⟩
      let ci' : Fin k := ⟨i'.val, lt_trans hi' hik⟩
      have hne : ci ≠ ci' := by
        intro e
        have h3 : ci.val = ci'.val := congrArg Fin.val e
        have h4 : i.val = i'.val := h3
        omega
      have e2 : (rowShift r n C σ i i' t).mapMatrix A =
          A.updateCol ci (fun b => A b ci + (MvPolynomial.C t : MvPolynomial (Letter T r n) C) • A b ci') := by
        refine Matrix.ext fun b c => ?_
        rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateCol_apply]
        simp only [hA, Matrix.of_apply]
        by_cases hcc : c = ci
        · subst hcc
          rw [if_pos rfl, smul_eq_mul]
          exact shift_add Φ σ w lt colf hΦ hlt i i' t _ _ _ rfl rfl
        · rw [if_neg hcc]
          refine shift_same Φ σ w lt colf hΦ hlt σ i i' t _ _ ?_
          rintro ⟨_, e⟩
          exact hcc (Fin.ext e)
      rw [e2, Matrix.det_updateCol_add_smul_self A hne]
    · have e2 : (rowShift r n C σ i i' t).mapMatrix A = A := by
        refine Matrix.ext fun b c => ?_
        rw [AlgHom.mapMatrix_apply, Matrix.map_apply]
        simp only [hA, Matrix.of_apply]
        refine shift_same Φ σ0 w lt colf hΦ hlt σ i i' t _ _ ?_
        rintro ⟨e0, e⟩
        apply hc
        refine ⟨e0, ?_⟩
        have : c.val = i.val := e
        omega
      rw [e2]
  · simp

end Atom

section Fam

variable {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
  {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N} {n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

def trueT (g : Fin 2) (s : ZMod 2) : ZMod 2 := if g = 0 then s else s + 1

theorem SelfConjugatePlaceSetting.en_fst (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2)
    (q : Fin ((X o).rkF g s)) : ((F o).en g s q).1 = trueT g s := by
  have h1 := (F o).en_ty g s q
  rw [H.hty o g] at h1
  unfold trueT
  generalize ((F o).en g s q).1 = u at h1 ⊢
  split_ifs at h1 ⊢ with hg
  · exact h1
  · subst h1
    have h2 : (1 : ZMod 2) + 1 = 0 := rfl
    rw [add_assoc, h2, add_zero]


variable (r tau gm) in
def PsiS (o : Orb) {M : ℕ} (col : Fin M → Fin N) :
    MvPolynomial (Fin M × WV fun _ => IIs r tau o) C →ₐ[C] MvPolynomial (Letter T r n) C :=
  (subG r tau gm plc).comp (rename fun x : Fin M × WV fun _ => IIs r tau o =>
    ((col x.1, (⟨o, x.2⟩ : WVO fun o (_ : Fin 2) => IIs r tau o))))

theorem SelfConjugatePlaceSetting.inv_minor (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) {M : ℕ}
    (col : Fin M → Fin N) (k : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k))) =
      PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k)) := by
  refine rowShift_minor_lin ((PsiS r tau gm plc o col).comp (rename ((F o).letter g s))) (tau o (trueT g s))
    (fun _ q => gm o (trueT g s) q g)
    (fun x q => ⟨tau o ((F o).en g s x.2).1, ((F o).en g s x.2).2, plc (col x.1, q)⟩) (fun ρ q => plc (col ρ, q)) ?_ ?_
    σ i i' hi t k
  · intro x
    rw [AlgHom.comp_apply, rename_X]
    unfold PsiS
    rw [AlgHom.comp_apply, rename_X]
    unfold subG
    rw [aeval_X]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e2 : gm o ((F o).en g s x.2).1 q g = gm o (trueT g s) q g := by rw [H.en_fst]
    exact congrArg (fun z : C => MvPolynomial.C z * MvPolynomial.X
      (⟨tau o ((F o).en g s x.2).1, ((F o).en g s x.2).2, plc (col x.1, q)⟩ : Letter T r n)) e2
  · intro ρ c q
    show (tau o ((F o).en g s c).1, ((F o).en g s c).2.val, plc (col ρ, q)) = _
    simp only [Prod.mk.injEq]
    exact ⟨congrArg (tau o) (H.en_fst o g s c), H.std o g s c, trivial⟩

theorem SelfConjugatePlaceSetting.inv_mon (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) {M : ℕ}
    (col : Fin M → Fin N) (e : ℕ → ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col (rename ((F o).letter g s) (monP C M ((X o).rkF g s) e))) =
      PsiS r tau gm plc o col (rename ((F o).letter g s) (monP C M ((X o).rkF g s) e)) := by
  unfold monP
  simp only [map_prod, map_pow]
  exact Finset.prod_congr rfl fun k _ => by rw [H.inv_minor plc o g s col k σ i i' hi t]

theorem SelfConjugatePlaceSetting.inv_bi (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g g' : Fin 2) (s s' : ZMod 2) {M : ℕ}
    (col : Fin M → Fin N) (k e1 e2 : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col
      (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C M ((X o).rkF g' s') k) ^ e2)) =
      PsiS r tau gm plc o col
      (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C M ((X o).rkF g' s') k) ^ e2) := by
  simp only [map_mul, map_pow]
  rw [H.inv_minor plc o g s col k σ i i' hi t, H.inv_minor plc o g' s' col k σ i i' hi t]

theorem SelfConjugatePlaceSetting.inv_ch (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) {M : ℕ}
    (col : Fin M → Fin N) (k e1 : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col
      (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1)) =
      PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1) := by
  rw [map_pow, map_pow, H.inv_minor plc o g s col k σ i i' hi t]

theorem SelfConjugatePlaceSetting.inv_monAll (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) {M : ℕ}
    (col : Fin M → Fin N) (e : ZMod 2 → ℕ → ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col
      (∏ s : ZMod 2, rename ((F o).letter g s) (monP C M ((X o).rkF g s) (e s)))) =
      PsiS r tau gm plc o col (∏ s : ZMod 2, rename ((F o).letter g s) (monP C M ((X o).rkF g s) (e s))) := by
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun s _ => H.inv_mon plc o g s col (e s) σ i i' hi t

theorem SelfConjugatePlaceSetting.inv_poly (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (b : GlobalTheory 2) (col : Fin (b.what₂ (X o).n) → Fin N)
    (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col (b.poly (X o) (F o))) = PsiS r tau gm plc o col (b.poly (X o) (F o)) := by
  cases b with
  | bi g s e y => exact H.inv_bi plc o g (1 - g) s (s + (e : ZMod 2)) col (X o).n _ _ σ i i' hi t
  | ch g s u => exact H.inv_ch plc o g s col (X o).n u σ i i' hi t
  | mon g e M => exact H.inv_monAll plc o g col e σ i i' hi t

theorem subG_blkProd :
    subG r tau gm plc (blkProd X F N L pl) =
      ∏ o, ∏ i, PsiS r tau gm plc o (fun ρ => plAt N pl o ⟨i, ρ⟩) ((blkAt L o i).poly (X o) (F o)) := by
  unfold blkProd
  rw [map_prod]
  refine Finset.prod_congr rfl fun o _ => ?_
  unfold toAll prodAll
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rename_rename]
  rfl

end Fam

theorem isotropic_to_standard_substitution_invariant : IsotropicToStdSubstLineInvariant := by
  intro C _ V T r cc a Orb _ tau gm J _ X F gaC N L pl H n plc σ i i' hi t
  rw [subG_blkProd, map_prod]
  refine Finset.prod_congr rfl fun o _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun j _ => H.inv_poly plc o _ _ σ i i' hi t

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePNabMapSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.MapFB

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {K C : Type} [Field K] [Field C] (φ : K →+* C) {d : ℕ}

theorem constantCoeff_eval_single {n : ℕ} (a : Pt K n d) (ha : ∀ i, constantCoeff (a i) = 0) (f : PS K 1 d) :
    constantCoeff (ev ![a] f) = constantCoeff f :=
  cc_ev_eq _ (by intro j i; fin_cases j; simp [ha]) f

theorem map_pderiv {σ : Type} (x : σ) (f : MvPowerSeries σ K) :
    MvPowerSeries.map φ (pderiv x f) = pderiv x (MvPowerSeries.map φ f) := by
  ext n
  simp [coeff_pderiv, coeff_map]

theorem map_DofN (F : Fin d → PS K 2 d) {n : ℕ} (b : Fin n) (u : Fin d → K) (f : PS K n d) :
    MvPowerSeries.map φ (DofN F b u f) =
      DofN (fun j => MvPowerSeries.map φ (F j)) b (fun i => φ (u i)) (MvPowerSeries.map φ f) := by
  unfold DofN
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, MvPowerSeries.map_C,
    map_ev2 φ (pt K d b) 0 (fun i => cc_pt b i) zc_zero, mpt_pt, mpt_zero, map_pderiv]

theorem map_iter_DofN (F : Fin d → PS K 2 d) {n : ℕ} (b : Fin n) (u : Fin d → K) (m : ℕ) (f : PS K n d) :
    MvPowerSeries.map φ ((DofN F b u)^[m] f) =
      (DofN (fun j => MvPowerSeries.map φ (F j)) b (fun i => φ (u i)))^[m] (MvPowerSeries.map φ f) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_DofN, ih]

theorem map_DmonN (F : Fin d → PS K 2 d) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → K) (m : ι →₀ ℕ) (f : PS K n d) :
    MvPowerSeries.map φ (DmonN F cp u m f) =
      DmonN (fun j => MvPowerSeries.map φ (F j)) cp (fun l i => φ (u l i)) m (MvPowerSeries.map φ f) := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, List.foldr_cons, map_iter_DofN, ih]

theorem map_DpolyN (F : Fin d → PS K 2 d) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → K) (P : MvPolynomial ι K) (f : PS K n d) :
    MvPowerSeries.map φ (DpolyN F cp u P f) =
      DpolyN (fun j => MvPowerSeries.map φ (F j)) cp (fun l i => φ (u l i)) (MvPolynomial.map φ P)
        (MvPowerSeries.map φ f) := by
  unfold DpolyN
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, MvPolynomial.support_map_of_injective P φ.injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, MvPowerSeries.map_C, MvPolynomial.coeff_map, map_DmonN]

theorem map_expS' [Algebra ℚ K] [Algebra ℚ C] {n : ℕ} (f : PS K n d) (hf : constantCoeff f = 0) :
    MvPowerSeries.map φ (FB.expS K f) = FB.expS C (MvPowerSeries.map φ f) := by
  unfold FB.expS
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf), PowerSeries.map_exp]

theorem map_nabValN [Algebra ℚ K] [Algebra ℚ C] {O : Type} [CommRing O] [StarRing O]
    (B : FB K d O) (B' : FB C d O) (hF : ∀ j, B'.G.F j = MvPowerSeries.map φ (B.G.F j))
    (hA : ∀ a j, B'.A.act a j = MvPowerSeries.map φ (B.A.act a j)) (h : PS K 2 d)
    (hh : constantCoeff h = 0) (w0 : O) (m : ℕ) {n : ℕ} (f : PS K n d) {ι : Type} [Fintype ι]
    (cp : ι → Fin n) (u : ι → Fin d → K) (P : MvPolynomial ι K) :
    nabValN B' C (MvPowerSeries.map φ h) w0 m (MvPowerSeries.map φ f) cp (fun l i => φ (u l i))
        (MvPolynomial.map φ P) = φ (nabValN B K h w0 m f cp u P) := by
  unfold nabValN
  rw [← constantCoeff_map]
  congr 1
  have e1 : B.FK K = B.G.F := rfl
  have e2 : B'.FK C = fun j => MvPowerSeries.map φ (B.G.F j) := funext hF
  have eA : mpt φ (B.A.act w0) = B'.actK C w0 := by
    funext j; exact (hA w0 j).symm
  have eK : B.actK K w0 = B.A.act w0 := rfl
  have p0 : ∀ i, constantCoeff (pt K d (0 : Fin 1) i) = 0 := cc_pt (R := K) (d := d) 0
  have q0 : ∀ i, constantCoeff (comp1 (B.A.act w0) (pt K d (0 : Fin 1)) i) = 0 :=
    cc_comp1 (B.A.act w0) (B.A.const w0) (pt K d (0 : Fin 1)) p0
  have hL : MvPowerSeries.map φ (B.hL K h w0) = B'.hL C (MvPowerSeries.map φ h) w0 := by
    unfold FB.hL
    rw [eK, map_ev2 φ (pt K d 0) (comp1 (B.A.act w0) (pt K d 0)) p0 q0, mpt_pt,
      mpt_comp1 φ (B.A.act w0) (pt K d 0) p0, mpt_pt, eA]
  have hcL : constantCoeff (B.hL K h w0) = 0 := by
    unfold FB.hL
    rw [eK, constantCoeff_eval_pair (pt K d 0) (comp1 (B.A.act w0) (pt K d 0)) p0 q0, hh]
  have hcb : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt K d b] (B.hL K h w0)) = 0 := fun b => by
    rw [constantCoeff_eval_single (pt K d b) (cc_pt (R := K) (d := d) b), hcL]
  have hcs : constantCoeff ((m : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Nat.cast_smul_eq_nsmul, map_nsmul, map_sum, Finset.sum_eq_zero fun b _ => hcb b, smul_zero]
  have hsum : ∑ b : Fin n, MvPowerSeries.map φ (ev (n := n) ![pt K d b] (B.hL K h w0)) =
      ∑ b : Fin n, ev (n := n) ![pt C d b] (B'.hL C (MvPowerSeries.map φ h) w0) :=
    Finset.sum_congr rfl fun b _ => by
      rw [map_ev1 φ (pt K d b) (cc_pt (R := K) (d := d) b), mpt_pt, hL]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, e2, map_DpolyN, map_mul, map_expS' φ _ hcs, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul,
    map_nsmul, map_sum, hsum]

end Formalism.L2.FormalSeriesBounds.MapFB

namespace Formalism.L2.FormalSeriesBounds

open MvPowerSeries MapFB Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

theorem nabMapSt_holds : NabMapSt Xo c := by
  intro T io y C3 C _ _ V ι k Y hY a n f P
  have hga : (a3B C3).IsCanonGauge T.Fr (a3h C3) := by
    let := io.toAlgebra
    exact C3.ch.gauge
  have hcc : constantCoeff (a3h C3) = 0 := by
    have e := congrArg constantCoeff hga.ax0
    rwa [constantCoeff_eval_pair _ _ zc_zero (by simp), map_zero] at e
  unfold FBChart.nab chartDerivativeCoefficient
  rw [hY.h, hY.w0, hY.k]
  exact map_nabValN ι (a3B C3) Y.B hY.F hY.act (a3h C3) hcc H.w0 k f _ _ P

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieSelfCuts
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

section Core

variable {Orb : Type} {d : ℕ} [NeZero d]

structure LabSGeoCore (C3 : IntChart T io y) (ι : T.Fr →+* C) (Y : FBChart C V (𝓞 E) (chD C3.ch))
    (lab : LabS E C Orb d) : Prop where
  e_eig : ∀ o (x : lab.II Dw o) a, linAct (Y.B.A.act a) (selfLieBasisVector C3 ι lab o x) =
    emA3 io ι (lab.tau o x.1) a • selfLieBasisVector C3 ι lab o x
  e_sat : ∀ o, ∃ w : Fin (chD C3.ch) → lab.II Dw o → C, (∀ x q, V.Ge 0 (w x q)) ∧
    ∀ q q' : lab.II Dw o, ∑ x, selfLieBasisVector C3 ι lab o q x * w x q' = if q = q' then 1 else 0
  e_full : ∀ o a (v : Fin (chD C3.ch) → C), (∀ x, linAct (Y.B.A.act x) v = emA3 io ι (lab.tau o a) x • v) →
    ∃ b : lab.II Dw o → C, (∀ q, q.1 ≠ a → b q = 0) ∧ v = ∑ q, b q • selfLieBasisVector C3 ι lab o q

theorem labSGeo_of (hstar : ∀ a : 𝓞 E, star a = H.bar a) {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι)
    {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d} (ha : LabSArith V io ι lab)
    (h : LabSGeoCore C3 ι Y lab) : LabSGeo C3 ι Y lab := by
  refine {
    em_int := fun _ _ x => embedding_integral ι _ x
    em_conj := ?_
    e_int := fun _ _ i => a3uvec_int C3 hι _ i
    e_eig := h.e_eig
    e_sat := h.e_sat
    e_full := h.e_full }
  intro o a x
  rw [← ha.conj o a]
  exact (embedding_conjugate hstar ι _ x).symm

end Core

def RankMaximalSelfOfNondegenerate : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0),
    NDG Y → (Y.rawSelf p).RankHyp → ∀ Hc : ∀ g, (Y.rawSelf p).CartHyp V g, RawChart.RankMaximalCondition Hc

variable (Xo c)

theorem rank_maximal_self_charts_of_nondegenerate (h1 : RankMaximalSelfOfNondegenerate) (h2 : NondegenerateCharts Xo c) : RankMaximalSelfCharts Xo c :=
  fun hstar T io y C3 C _ _ V ι hι k Y hY _ d _ lab ha hg hr o Hc => by
    have hrank : (Y.rawSelf (selfOfLab ha hg o)).RankHyp := by
      refine { big_compl := (hr o).1, rk_big := ?_, rk_small := ?_ }
      · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab]
          convert (card_sigma_fst (fun b => Dw.mult (lab.tau o b)) a).trans ((hr o).2.1 a hb) using 2
          exact Finset.filter_congr (fun _ _ => Iff.rfl)
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
          exact (card_sigma_shift (fun b => Dw.mult (lab.tau o b)) lab.hd a).trans ((hr o).2.2.2.1 a hb)
      · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab]
          convert (card_sigma_fst (fun b => Dw.mult (lab.tau o b)) a).trans ((hr o).2.2.1 a hb) using 2
          exact Finset.filter_congr (fun _ _ => Iff.rfl)
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
          exact (card_sigma_shift (fun b => Dw.mult (lab.tau o b)) lab.hd a).trans ((hr o).2.2.2.2 a hb)
    exact h1 C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (h2 hstar T io y C3 C V ι hι k Y hY) hrank Hc

end Formalism.L2.FormalSeriesBounds
end
end

