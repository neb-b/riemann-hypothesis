module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PtEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SiegelAdmissibleToRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpecAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.TopUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.ValComapLtOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0326
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvCancel
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {m : ℕ}

omit [IsAlgClosure ℚ Ω] in
private theorem sl_sl (γ δ : SL(2, ℤ)) (f : X.K) :
    X.sl (ofSL (γ * δ)) f = X.sl (ofSL δ) (X.sl (ofSL γ) f) := by
  rw [map_mul, X.sl_mul]

omit [IsAlgClosure ℚ Ω] in
private theorem sl_inv (γ : SL(2, ℤ)) (f : X.K) : X.sl (ofSL γ⁻¹) (X.sl (ofSL γ) f) = f := by
  rw [← sl_sl, mul_inv_cancel, map_one, X.sl_one]

private theorem mv_comp (hm : 0 < m) (γ δ : SL(2, ℤ)) {u v : X.K} {P Q R : Pt X m} (hP : IsPt X m u v P)
    (hQ : IsPt X m (X.sl (ofSL γ) u) (X.sl (ofSL γ) v) Q)
    (hR : IsPt X m (X.sl (ofSL δ) (X.sl (ofSL γ) u)) (X.sl (ofSL δ) (X.sl (ofSL γ) v)) R) {f : X.Kˣ}
    (h1 : Mv X m (slR X (ofSL γ)) 1 P Q 1) (h2 : Mv X m (slR X (ofSL δ)) 1 Q R f) :
    Mv X m (slR X (ofSL (γ * δ))) 1 P R f := by
  have key := mvComp Ω ε X m hm (slR X (ofSL γ)) (slR X (ofSL δ)) 1 1 ((admB Ω ε X).1 _)
    ((admB Ω ε X).1 _) u v P Q R hP hQ hR 1 f h1 h2
  have he : (slR X (ofSL γ)).trans (slR X (ofSL δ)) = slR X (ofSL (γ * δ)) := by
    ext x
    show X.sl (ofSL δ) (X.sl (ofSL γ) x) = X.sl (ofSL (γ * δ)) x
    exact (sl_sl X γ δ x).symm
  rw [he, mul_one, map_one, one_pow, one_mul] at key
  exact key

private theorem mv_cancel (hm : 0 < m) (γ δ : SL(2, ℤ)) {u v : X.K} {P Q R : Pt X m} (hP : IsPt X m u v P)
    (hQ : IsPt X m (X.sl (ofSL γ) u) (X.sl (ofSL γ) v) Q)
    (hR : IsPt X m (X.sl (ofSL δ) (X.sl (ofSL γ) u)) (X.sl (ofSL δ) (X.sl (ofSL γ) v)) R)
    (h1 : Mv X m (slR X (ofSL γ)) 1 P Q 1) (h2 : Mv X m (slR X (ofSL (γ * δ))) 1 P R 1) :
    Mv X m (slR X (ofSL δ)) 1 Q R 1 := by
  have hA := admB Ω ε X
  obtain ⟨f, -, hf⟩ := (mvEx Ω ε X m hm (slR X (ofSL δ)) 1 (hA.1 _) (X.sl (ofSL γ) u)
    (X.sl (ofSL γ) v) Q hQ).1 R hR
  have h3 := mv_comp X hm γ δ hP hQ hR h1 hf
  have hR' : IsPt X m (X.sl (ofSL (γ * δ)) u) (X.sl (ofSL (γ * δ)) v) R := by
    rw [sl_sl X γ δ u, sl_sl X γ δ v]
    exact hR
  obtain ⟨k, hk⟩ := ((mvEx Ω ε X m hm (slR X (ofSL (γ * δ))) 1 (hA.1 _) u v P hP).2.2.2
    R hR' 1 f h2).mp h3
  refine ((mvEx Ω ε X m hm (slR X (ofSL δ)) 1 (hA.1 _) (X.sl (ofSL γ) u)
    (X.sl (ofSL γ) v) Q hQ).2.2.2 R hR f 1 hf).mpr ⟨k⁻¹, ?_⟩
  rw [hk, one_mul, inv_pow, mul_inv_cancel]

omit [IsAlgClosure ℚ Ω] in
private theorem rep_ex : ∃ (r : X.K × X.K → X.K × X.K) (g : X.K × X.K → SL(2, ℤ)),
    (∀ p, X.sl (ofSL (g p)) (r p).1 = p.1 ∧ X.sl (ofSL (g p)) (r p).2 = p.2) ∧
    ∀ (p : X.K × X.K) (γ : SL(2, ℤ)), r (X.sl (ofSL γ) p.1, X.sl (ofSL γ) p.2) = r p := by
  let S : Setoid (X.K × X.K) :=
    { r := fun p q => ∃ g : SL(2, ℤ), X.sl (ofSL g) p.1 = q.1 ∧ X.sl (ofSL g) p.2 = q.2
      iseqv := ⟨fun p => ⟨1, by rw [map_one, X.sl_one], by rw [map_one, X.sl_one]⟩,
        fun ⟨g, h1, h2⟩ => ⟨g⁻¹, by rw [← h1, sl_inv], by rw [← h2, sl_inv]⟩,
        fun ⟨g, h1, h2⟩ ⟨k, k1, k2⟩ => ⟨g * k, by rw [sl_sl, h1, k1], by rw [sl_sl, h2, k2]⟩⟩ }
  refine ⟨fun p => (Quotient.mk S p).out, fun p => Classical.choose (Quotient.mk_out (s := S) p),
    fun p => Classical.choose_spec (Quotient.mk_out (s := S) p), fun p γ => ?_⟩
  show (Quotient.mk S _).out = (Quotient.mk S p).out
  rw [Quotient.sound (s := S) ⟨γ⁻¹, sl_inv X γ p.1, sl_inv X γ p.2⟩]

end

theorem UpperTheory.V.Z.Kato.Sym.secEx :
    UpperTheory.V.Z.Kato.Sym.SecEx := by
  intro Ω _ _ _ ε X m hm
  obtain ⟨r, g, hg, hr⟩ := rep_ex X
  have hA := admB Ω ε X
  haveI : Nonempty (Pt X m) := ⟨⟨0, 0, fun _ => 0⟩⟩
  have hUsl : ∀ (γ : SL(2, ℤ)) (a : X.K), IsU X a → IsU X (X.sl (ofSL γ) a) :=
    fun γ a ha => (hA.2.2.2.2.2.1 _ _ (hA.1 (ofSL γ))).1 a ha
  let Good : X.K → X.K → Pt X m → Prop := fun a b P => IsPt X m a b P ∧
    ∀ γ : SL(2, ℤ), X.sl (ofSL γ) a = a → X.sl (ofSL γ) b = b → Mv X m (slR X (ofSL γ)) 1 P P 1
  let P0 : X.K → X.K → Pt X m := fun a b => Classical.epsilon (Good a b)
  have hP0 : ∀ a b, IsU X a → IsU X b → Good a b (P0 a b) :=
    fun a b ha hb => Classical.epsilon_spec (ptEx Ω ε X m hm a b ha hb)
  have hrep : ∀ a b, X.sl (ofSL (g (a, b))) (r (a, b)).1 = a ∧
      X.sl (ofSL (g (a, b))) (r (a, b)).2 = b := fun a b => hg (a, b)
  have hrU : ∀ a b, IsU X a → IsU X b → IsU X (r (a, b)).1 ∧ IsU X (r (a, b)).2 := by
    intro a b ha hb
    have e1 := congrArg (fun x => X.sl (ofSL (g (a, b))⁻¹) x) (hrep a b).1
    have e2 := congrArg (fun x => X.sl (ofSL (g (a, b))⁻¹) x) (hrep a b).2
    simp only [sl_inv] at e1 e2
    rw [e1, e2]
    exact ⟨hUsl _ a ha, hUsl _ b hb⟩
  let t : X.K → X.K → Pt X m := fun a b => Classical.epsilon (fun Q => IsPt X m a b Q ∧
    Mv X m (slR X (ofSL (g (a, b)))) 1 (P0 (r (a, b)).1 (r (a, b)).2) Q 1)
  have ht : ∀ a b, IsU X a → IsU X b → IsPt X m a b (t a b) ∧
      Mv X m (slR X (ofSL (g (a, b)))) 1 (P0 (r (a, b)).1 (r (a, b)).2) (t a b) 1 := by
    intro a b ha hb
    obtain ⟨h1, h2⟩ := hrU a b ha hb
    obtain ⟨Q, hQ, hM⟩ := (mvEx Ω ε X m hm (slR X (ofSL (g (a, b)))) 1 (hA.1 _) _ _ _
      (hP0 _ _ h1 h2).1).2.1
    change IsPt X m (X.sl (ofSL (g (a, b))) (r (a, b)).1)
      (X.sl (ofSL (g (a, b))) (r (a, b)).2) Q at hQ
    rw [(hrep a b).1, (hrep a b).2] at hQ
    exact Classical.epsilon_spec (p := fun Q => IsPt X m a b Q ∧
      Mv X m (slR X (ofSL (g (a, b)))) 1 (P0 (r (a, b)).1 (r (a, b)).2) Q 1) ⟨Q, hQ, hM⟩
  refine ⟨t, fun u v hu hv => ⟨(ht u v hu hv).1, fun γ => ?_⟩⟩
  have hu' := hUsl γ u hu
  have hv' := hUsl γ v hv
  have hrr : r (X.sl (ofSL γ) u, X.sl (ofSL γ) v) = r (u, v) := hr (u, v) γ
  obtain ⟨hQt, hMa⟩ := ht u v hu hv
  obtain ⟨hRt, hMb⟩ := ht _ _ hu' hv'
  obtain ⟨q1, q2⟩ := hrU u v hu hv
  have hgood := hP0 _ _ q1 q2
  obtain ⟨e1, e2⟩ := hrep u v
  obtain ⟨f1, f2⟩ := hrep (X.sl (ofSL γ) u) (X.sl (ofSL γ) v)
  rw [hrr] at hMb f1 f2
  have hs1 : X.sl (ofSL (g (u, v) * γ * (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v))⁻¹)) (r (u, v)).1
      = (r (u, v)).1 := by
    rw [sl_sl X (g (u, v) * γ), sl_sl X (g (u, v)) γ, e1]
    have k := sl_inv X (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v)) (r (u, v)).1
    rw [f1] at k
    exact k
  have hs2 : X.sl (ofSL (g (u, v) * γ * (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v))⁻¹)) (r (u, v)).2
      = (r (u, v)).2 := by
    rw [sl_sl X (g (u, v) * γ), sl_sl X (g (u, v)) γ, e2]
    have k := sl_inv X (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v)) (r (u, v)).2
    rw [f2] at k
    exact k
  have stab := hgood.2 _ hs1 hs2
  have comp := mv_comp X hm _ (g (X.sl (ofSL γ) u, X.sl (ofSL γ) v)) hgood.1
    (by rw [hs1, hs2]; exact hgood.1) (by rw [hs1, hs2, f1, f2]; exact hRt) stab hMb
  rw [inv_mul_cancel_right] at comp
  exact mv_cancel X hm (g (u, v)) γ hgood.1 (by rw [e1, e2]; exact hQt)
    (by rw [e1, e2]; exact hRt) hMa comp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PLev
section
noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

theorem pLev : PLev := by
  unfold PLev
  intro Ω _ _ _ ε X m c d k M hm hc hd hc6 hd6 hlv t w' w ht hw' hw
  obtain ⟨hkM, hck, hdk⟩ := hlv
  have hM : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hkM)
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hkM)
  obtain ⟨-, hgal, -, -, -, -, -, hUn⟩ := admB Ω ε X
  obtain ⟨hgr, hok, -, hup⟩ := rowB Ω M hM
  obtain ⟨-, hokK, -, -⟩ := rowB Ω (k * M) hkM
  obtain ⟨hupQ, hupOk, hupgr, -⟩ := hup k hk
  have hsgup : ∀ e : ℕ, 1 < e → e.Coprime 6 → e.Coprime (k * M) → ∀ z : Row M, z ≠ 0 →
      up k M z ≠ 0 → sg X e (k * M) (up k M z) = sg X e M z := by
    intro e he he6 hek z hz hz'
    have hem : e.Coprime M := Nat.Coprime.coprime_dvd_right (dvd_mul_left M k) hek
    rw [← (sgB Ω ε X e (k * M) he he6 hkM hek (up k M z) hz').2.2.2 (toQ M z)
      (fun i => ⟨0, by simp [hupQ z]⟩)]
    exact (sgB Ω ε X e M he he6 hM hem z hz).2.2.2 (toQ M z) (fun i => ⟨0, by simp⟩)
  have hcM : c.Coprime M := Nat.Coprime.coprime_dvd_right (dvd_mul_left M k) hck
  have hdM : d.Coprime M := Nat.Coprime.coprime_dvd_right (dvd_mul_left M k) hdk
  unfold Coh Eqv CobBy
  refine ⟨fun _ _ => (1 : X.Kˣ), ?_, ?_⟩
  · intro x y _
    refine ⟨(hUn m).1, fun γ => ⟨1, by simp [slU]⟩⟩
  · intro s x y hxy
    have hxy1 : Ok (gr M s⁻¹ x) (gr M s⁻¹ y) := (hok x y hxy).2.2.1 s⁻¹
    have hupxy := hupOk x y hxy
    have hupxy1 := hupOk _ _ hxy1
    have hx := (hok x y hxy).1
    have hy := (hok x y hxy).2.1
    have hx1 := (hok _ _ hxy1).1
    have hy1 := (hok _ _ hxy1).2.1
    have hux := (hokK _ _ hupxy).1
    have huy := (hokK _ _ hupxy).2.1
    have hux1 := (hokK _ _ hupxy1).1
    have huy1 := (hokK _ _ hupxy1).2.1
    obtain ⟨-, hwMv⟩ := hw s x y hxy
    obtain ⟨-, hw'Mv⟩ := hw' s (up k M x) (up k M y) hupxy
    rw [hupgr s⁻¹ x, hupgr s⁻¹ y, hsgup c hc hc6 hck _ hx1 hux1, hsgup d hd hd6 hdk _ hy1 huy1,
      hsgup c hc hc6 hck _ hx hux, hsgup d hd hd6 hdk _ hy huy] at hw'Mv
    have hgx : ∀ z : Row M, gr M s (gr M s⁻¹ z) = z := by
      intro z
      rw [← (hgr s s⁻¹ z).1, mul_inv_cancel, (hgr 1 1 z).2]
    have hτu : X.gal s (sg X c M (gr M s⁻¹ x)) = sg X c M x := by
      rw [(sgB Ω ε X c M hc hc6 hM hcM _ hx1).2.2.1 s, hgx]
    have hτv : X.gal s (sg X d M (gr M s⁻¹ y)) = sg X d M y := by
      rw [(sgB Ω ε X d M hd hd6 hM hdM _ hy1).2.2.1 s, hgx]
    have hP := (ht (sg X c M (gr M s⁻¹ x)) (sg X d M (gr M s⁻¹ y))
      (sgB Ω ε X c M hc hc6 hM hcM _ hx1).1 (sgB Ω ε X d M hd hd6 hM hdM _ hy1).1).1
    have hQ := (ht (sg X c M x) (sg X d M y)
      (sgB Ω ε X c M hc hc6 hM hcM _ hx).1 (sgB Ω ε X d M hd hd6 hM hdM _ hy).1).1
    have key := (mvEx Ω ε X m hm (X.gal s) s (hgal s) _ _ _ hP).2.2.2 _
      (by rw [hτu, hτv]; exact hQ) _ (w' s (up k M x) (up k M y)) hwMv
    have htw : tw X m M s (fun _ _ => (1 : X.Kˣ)) x y = 1 := by simp [tw]
    rw [htw, mul_one, div_one]
    exact key.1 hw'Mv

end UpperTheory.V.Z.Kato.Sym

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PSymb
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.pSymb :
    UpperTheory.V.Z.Kato.Sym.PSymb := by
  intro Ω _ _ _ ε X m c d M hm hc hd hc6 hd6 hL t ht
  unfold UpperTheory.V.Z.Kato.Sym.Lv at hL
  unfold UpperTheory.V.Z.Kato.Sym.IsSec at ht
  obtain ⟨hM, hcM, hdM⟩ := hL
  obtain ⟨hgr, hok, -⟩ := UpperTheory.V.Z.Kato.Sym.rowB Ω M hM
  obtain ⟨-, hadm, -⟩ := UpperTheory.V.Z.Kato.Sym.admB Ω ε X
  have key : ∀ (s : Gal(Ω/ℚ)) (x y : UpperTheory.V.Z.Kato.Sym.Row M), UpperTheory.V.Z.Kato.Sym.Ok x y →
      ∃ f ∈ X.Un m, UpperTheory.V.Z.Kato.Sym.Mv X m (X.gal s) s
        (t (UpperTheory.V.Z.Kato.Sym.sg X c M (UpperTheory.V.Z.Kato.Sym.gr M s⁻¹ x)) (UpperTheory.V.Z.Kato.Sym.sg X d M (UpperTheory.V.Z.Kato.Sym.gr M s⁻¹ y)))
        (t (UpperTheory.V.Z.Kato.Sym.sg X c M x) (UpperTheory.V.Z.Kato.Sym.sg X d M y)) f := by
    intro s x y hxy
    obtain ⟨hx0, hy0, -⟩ := hok _ _ ((hok x y hxy).2.2.1 s⁻¹)
    have hsx := UpperTheory.V.Z.Kato.Sym.sgB Ω ε X c M hc hc6 hM hcM _ hx0
    have hsy := UpperTheory.V.Z.Kato.Sym.sgB Ω ε X d M hd hd6 hM hdM _ hy0
    have hP := (ht _ _ hsx.1 hsy.1).1
    have hx1 := UpperTheory.V.Z.Kato.Sym.sgB Ω ε X c M hc hc6 hM hcM x (hok x y hxy).1
    have hy1 := UpperTheory.V.Z.Kato.Sym.sgB Ω ε X d M hd hd6 hM hdM y (hok x y hxy).2.1
    have ex := UpperTheory.V.Z.Kato.Sym.mvEx Ω ε X m hm (X.gal s) s (hadm s) _ _ _ hP
    have ex1 := ex.1 (t (UpperTheory.V.Z.Kato.Sym.sg X c M x) (UpperTheory.V.Z.Kato.Sym.sg X d M y))
    rw [hsx.2.2.1, hsy.2.2.1, ← (hgr s s⁻¹ x).1, ← (hgr s s⁻¹ y).1, mul_inv_cancel, (hgr 1 1 x).2, (hgr 1 1 y).2] at ex1
    exact ex1 (ht _ _ hx1.1 hy1.1).1
  classical
  refine ⟨fun s x y => if h : UpperTheory.V.Z.Kato.Sym.Ok x y then Classical.choose (key s x y h) else 1, ?_⟩
  unfold UpperTheory.V.Z.Kato.Sym.IsSymb
  intro s x y hxy
  simp only [dif_pos hxy]
  exact Classical.choose_spec (key s x y hxy)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PtTop
section
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

attribute [local instance] algMdl

theorem UpperTheory.V.Z.Kato.Sym.ptTop :
    UpperTheory.V.Z.Kato.Sym.PtTop := by
  intro Ω _ _ _ ε X l n M hl hM hd u v hu hv huF hvF
  obtain ⟨e, he⟩ := isoEx Ω ε X M
  obtain ⟨h1, h2⟩ := TopEta.spec_of_units X hM.ne' hl.ne_zero hd (isTopUnit X M hu huF) (isTopUnit X M hv hvF)
  have hη := isTopEta_topEta X M h1
  refine ⟨_, ptIs Ω ε X l n M hl hM hd u v hu hv huF hvF e he _ hη, ptGam Ω ε X l n M hl hM hd u v hu hv huF hvF e he _ hη,
    fun s hs => ?_⟩
  have hw := h2 (topLift X M s)⁻¹
  have h0 : wGen X M l n u v s ≠ 0 := fun h => hw.1 (Subtype.ext h)
  exact ⟨Units.mk0 _ h0, rfl, ptGal Ω ε X l n M hl hM hd u v hu hv huF hvF e he _ hη s hs _ hw _ rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.Square
section
noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

private theorem square {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (m : ℕ)
    (hm : 0 < m) (τ : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω) (hτ : admitted X τ s) (u v : X.K) (P Q P' Q' : Pt X m)
    (hP : IsPt X m u v P) (hQ : IsPt X m u v Q) (hP' : IsPt X m (τ u) (τ v) P') (hQ' : IsPt X m (τ u) (τ v) Q')
    (a a' f g : X.Kˣ) (ha : Mv X m (RingEquiv.refl _) 1 P Q a) (ha' : Mv X m (RingEquiv.refl _) 1 P' Q' a')
    (hf : Mv X m τ s P P' f) (hg : Mv X m τ s Q Q' g) :
    Cgr m (f ^ (1 : ZMod m).val * a') (unU X τ a ^ (cyc m s).val * g) := by
  have hr : admitted X (RingEquiv.refl _) 1 := (admB Ω ε X).2.2.1
  have h1 : cyc m (1 : Ω ≃ₐ[ℚ] Ω) = 1 := ((lgB Ω ε X m hm).2.2.2.2.2.2 1 1).2.1
  have A := mvComp Ω ε X m hm (RingEquiv.refl _) τ 1 s hr hτ u v P Q Q' hP hQ hQ' a g ha hg
  have B := mvComp Ω ε X m hm τ (RingEquiv.refl _) s 1 hτ hr u v P P' Q' hP hP' hQ' f a' hf ha'
  rw [mul_one] at A
  rw [one_mul, h1] at B
  exact ((mvEx Ω ε X m hm τ s hτ u v P hP).2.2.2 Q' hQ' _ _ A).1 B

theorem cmp : Cmp := by
  intro Ω _ _ _ ε X m M hm hM U V R Q F F' hRQ hF
  obtain ⟨hgr, hok, -⟩ := rowB Ω M hM
  obtain ⟨-, hadm, hrefl, -⟩ := admB Ω ε X
  have c1 := ((lgB Ω ε X m hm).2.2.2.2.2.2 1 1).2.1
  have key : ∀ x y : Row M, Ok x y → ∃ b ∈ X.Un m, Mv X m (RingEquiv.refl _) 1 (R x y) (Q x y) b := by
    intro x y hxy
    exact (mvEx Ω ε X m hm _ 1 hrefl _ _ _ (hRQ x y hxy).1).1 _ (hRQ x y hxy).2
  have triv : m = 1 → ∀ f g : X.Kˣ, Cgr m f g := by
    rintro rfl f g
    unfold Cgr
    exact ⟨g⁻¹ * f, by simp⟩
  classical
  let a : Row M → Row M → X.Kˣ := fun x y => if h : Ok x y then Classical.choose (key x y h) else 1
  have ha : ∀ x y (h : Ok x y), a x y ∈ X.Un m ∧ Mv X m (RingEquiv.refl _) 1 (R x y) (Q x y) (a x y) := by
    intro x y h
    simp only [a, dif_pos h]
    exact Classical.choose_spec (key x y h)
  have hgal : ∀ s : Gal(Ω/ℚ), galU X s = unU X (X.gal s) := fun s => rfl
  refine ⟨a, ?_, ?_⟩
  · unfold CobBy
    intro s x y hxy
    have hxy0 : Ok (gr M s⁻¹ x) (gr M s⁻¹ y) := (hok x y hxy).2.2.1 s⁻¹
    obtain ⟨eU, eV, mR, mQ⟩ := hF s x y hxy
    have hsq := square X m hm (X.gal s) s (hadm s) _ _ _ _ (R x y) (Q x y)
      (hRQ _ _ hxy0).1 (hRQ _ _ hxy0).2 (by rw [eU, eV]; exact (hRQ x y hxy).1) (by rw [eU, eV]; exact (hRQ x y hxy).2)
      _ _ _ _ (ha _ _ hxy0).2 (ha x y hxy).2 mR mQ
    rcases eq_or_ne m 1 with h1 | h1
    · subst h1
      exact ⟨(F' s x y * tw X 1 M s a x y / a x y)⁻¹ * F s x y, by rw [pow_one, mul_inv_cancel_left]⟩
    haveI : Fact (1 < m) := ⟨by omega⟩
    rw [ZMod.val_one, pow_one] at hsq
    unfold Cgr at hsq
    obtain ⟨h, eh⟩ := hsq
    refine ⟨h, ?_⟩
    unfold tw
    rw [hgal, eq_mul_inv_of_mul_eq eh, div_eq_mul_inv]
    ac_rfl
  · intro x y hxy
    refine ⟨(ha x y hxy).1, ?_⟩
    intro τ x' y' hτ hxy' eU eV mR mQ
    rcases eq_or_ne m 1 with h1 | h1
    · exact triv h1 _ _
    haveI : Fact (1 < m) := ⟨by omega⟩
    have hsq := square X m hm τ 1 hτ (U x) (V y) (R x y) (Q x y) (R x' y') (Q x' y')
      (hRQ x y hxy).1 (hRQ x y hxy).2 (by rw [eU, eV]; exact (hRQ x' y' hxy').1) (by rw [eU, eV]; exact (hRQ x' y' hxy').2)
      _ _ 1 1 (ha x y hxy).2 (ha x' y' hxy').2 mR mQ
    simp only [c1, ZMod.val_one, pow_one, one_mul, mul_one] at hsq
    unfold Cgr at hsq ⊢
    obtain ⟨h, eh⟩ := hsq
    exact ⟨h⁻¹, by rw [eh, inv_pow, mul_inv_cancel_right]⟩

end UpperTheory.V.Z.Kato.Sym

end
end

