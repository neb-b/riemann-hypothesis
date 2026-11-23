module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Formalism.LocalToGlobal.Columns.Bundle0008
public import Formalism.LocalToGlobal.Columns.Bundle0005
public import Formalism.LocalToGlobal.Columns.Bundle0015

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.BrzoPairAtZeroRight
section
open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality Formalism.HermitianLatticesTheory

section Orth

variable {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K)

def brzo_perp (x : A.V) : Submodule (𝓞 K) A.V where
  carrier := {y | ∀ v, majAt A.b A.X v x y = 0}
  add_mem' := by
    intro a b ha hb v
    have h : majAt A.b A.X v x (a + b) = majAt A.b A.X v x a + majAt A.b A.X v x b := ((isSesq_maj A.b A.X) v).2.1 x a b
    rw [h, ha v, hb v, add_zero]
  zero_mem' := by
    intro v
    have h : majAt A.b A.X v x ((0 : K) • (0 : A.V)) = v.embedding (0 : K) * majAt A.b A.X v x 0 :=
      ((isSesq_maj A.b A.X) v).2.2.2 (0 : K) x 0
    simpa using h
  smul_mem' := by
    intro c y hy v
    have h : majAt A.b A.X v x (algebraMap (𝓞 K) K c • y) = v.embedding (algebraMap (𝓞 K) K c) * majAt A.b A.X v x y :=
      ((isSesq_maj A.b A.X) v).2.2.2 (algebraMap (𝓞 K) K c) x y
    rw [algebraMap_smul] at h
    rw [h, hy v, mul_zero]

variable {A} {γ : Type} [DecidableEq γ] (N : γ → Submodule (𝓞 K) A.V)

theorem brzo_orth_sup (horth : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c', ∀ v, majAt A.b A.X v x y = 0)
    (a : γ) (s : Finset γ) (ha : a ∉ s) : ∀ x ∈ N a, ∀ y ∈ ⨆ c ∈ s, N c,
    inner ℝ (realize A.b A.X x) (realize A.b A.X y) = 0 := by
  intro x hx y hy
  have hle : (⨆ c ∈ s, N c) ≤ brzo_perp A x :=
    iSup₂_le fun c hc z hz v => horth a c (fun h => ha (h ▸ hc)) x hx z hz v
  rw [Formalism.HN.HeightGram.inner_realize]
  exact Finset.sum_eq_zero fun v _ => by rw [hle hy v]; rfl

theorem hlat_orth_fin (hA : FrameOK A) (hfg : ∀ c, (N c).FG) (hne : ∀ c, N c ≠ ⊥)
    (horth : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c', ∀ v, majAt A.b A.X v x y = 0) (s : Finset γ) :
    Formalism.HN.deg (realize A.b A.X) (⨆ c ∈ s, N c) = ∑ c ∈ s, Formalism.HN.deg (realize A.b A.X) (N c) ∧
    (s.Nonempty → (⨆ c ∈ s, N c) ≠ ⊥ ∧ ∀ θ : ℝ, (∀ c ∈ s, Formalism.HN.muMax (realize A.b A.X) (N c) ≤ θ) →
      Formalism.HN.muMax (realize A.b A.X) (⨆ c ∈ s, N c) ≤ θ) := by
  have hlat : ∀ L : Submodule (𝓞 K) A.V, L.FG → Formalism.HN.IsLat (realize A.b A.X) L :=
    fun L hL => (Formalism.HN.plLat K A.V A.ι A.b A.X hA L hL).1
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, fun h => absurd h Finset.not_nonempty_empty⟩
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Finset.sum_empty]
    exact (Formalism.HN.satBasic (𝓞 K) A.V _ (realize A.b A.X) ⊥ (hlat ⊥ Submodule.fg_bot)).2.2.2.2.1
  | insert a s ha ih =>
    have hfs : (⨆ c ∈ s, N c).FG := Submodule.fg_biSup s N fun c _ => hfg c
    obtain ⟨-, h2, h3⟩ := (Formalism.HN.hnSum.{0, 0, 0, 0} (𝓞 K) A.V _ (realize A.b A.X)).2 (N a) (⨆ c ∈ s, N c) (hlat _ (hfg a)) (hlat _ hfs)
      (brzo_orth_sup N horth a s ha)
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    refine ⟨by rw [h2, ih.1], fun _ => ⟨fun h => hne a (eq_bot_iff.2 (h ▸ le_sup_left)), fun θ hθ => ?_⟩⟩
    by_cases hs : s.Nonempty
    · obtain ⟨i1, i2⟩ := ih.2 hs
      rw [(h3 (hne a) i1).1]
      exact max_le (hθ a (Finset.mem_insert_self _ _)) (i2 θ fun c hc => hθ c (Finset.mem_insert_of_mem hc))
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, sup_bot_eq]
      exact hθ a (Finset.mem_insert_self _ _)

theorem hlat_orth_sum [Fintype γ] [Nonempty γ] (hA : FrameOK A) (hfg : ∀ c, (N c).FG) (hne : ∀ c, N c ≠ ⊥)
    (horth : ∀ c c', c ≠ c' → ∀ x ∈ N c, ∀ y ∈ N c', ∀ v, majAt A.b A.X v x y = 0)
    (r : ℕ) (hr : 0 < r) (hrk : ∀ c, Formalism.HN.rkK (N c) = r) (hrkT : Formalism.HN.rkK (⨆ c, N c) = Fintype.card γ * r) :
    (withL A (⨆ c, N c)).mu = mean (fun c => (withL A (N c)).mu) ∧
    ∃ c, (withL A (⨆ c, N c)).muMax ≤ (withL A (N c)).muMax := by
  have hsup : (⨆ c, N c) = ⨆ c ∈ (Finset.univ : Finset γ), N c := by simp
  obtain ⟨h1, h2⟩ := hlat_orth_fin N hA hfg hne horth Finset.univ
  rw [← hsup] at h1 h2
  have hfT : (⨆ c, N c).FG := by rw [hsup]; exact Submodule.fg_biSup _ N fun c _ => hfg c
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hcard : (0 : ℝ) < (Fintype.card γ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hsl : ∀ c, Formalism.HN.slope (realize A.b A.X) (N c) =
      Formalism.HN.deg (realize A.b A.X) (N c) / ((Module.finrank ℚ K : ℝ) * r) := by
    intro c
    have := (Formalism.HN.plLat K A.V A.ι A.b A.X hA (N c) (hfg c)).2.1
    show Formalism.HN.deg (realize A.b A.X) (N c) / ((Formalism.HN.rk (realize A.b A.X) (N c) : ℕ) : ℝ) = _
    rw [this, hrk c]
    push_cast
    rfl
  have hslT : Formalism.HN.slope (realize A.b A.X) (⨆ c, N c) =
      (∑ c, Formalism.HN.deg (realize A.b A.X) (N c)) / ((Module.finrank ℚ K : ℝ) * (Fintype.card γ * r)) := by
    have := (Formalism.HN.plLat K A.V A.ι A.b A.X hA _ hfT).2.1
    show Formalism.HN.deg (realize A.b A.X) (⨆ c, N c) / ((Formalism.HN.rk (realize A.b A.X) (⨆ c, N c) : ℕ) : ℝ) = _
    rw [this, hrkT, h1]
    push_cast
    rfl
  constructor
  · show Formalism.HN.muDef A.b A.X (⨆ c, N c) = mean fun c => Formalism.HN.muDef A.b A.X (N c)
    unfold Formalism.HN.muDef mean
    rw [hslT]
    simp only [hsl]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
    field_simp
  · obtain ⟨c, -, hc⟩ := Finset.exists_max_image (Finset.univ : Finset γ)
      (fun c => Formalism.HN.muMax (realize A.b A.X) (N c)) Finset.univ_nonempty
    refine ⟨c, ?_⟩
    show Formalism.HN.muMaxDef A.b A.X (⨆ c, N c) ≤ Formalism.HN.muMaxDef A.b A.X (N c)
    unfold Formalism.HN.muMaxDef
    have := (h2 Finset.univ_nonempty).2 _ hc
    linarith

end Orth

section GSDOrth

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) (hf : S.Free)




end GSDOrth

section GSDOrth2

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

end GSDOrth2

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ChainFrmOk
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem frm_exists_c (p p0 : DecoF X.E n ST SG Q) (h : p.deco = p0.deco) :
    ∃ c : GLQ X.E n Q, p = ((1, 1, c) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • p0 := by
  refine ⟨fun P => ⟨(p.fr P)⁻¹ * p0.fr P, ?_⟩, ?_⟩
  · show ∀ x, ((p.fr P)⁻¹ * p0.fr P) x ∈ stdAt X.E n P.1 ↔ x ∈ stdAt X.E n P.1
    intro x
    have hx : p.1.2 P (((p.fr P)⁻¹ * p0.fr P) x) = p0.1.2 P x := LinearEquiv.apply_symm_apply _ _
    have h' : p.1.1 = p0.1.1 := h
    rw [← p.2 P, hx, h', p0.2 P]
  · apply Subtype.ext
    simp only [HSMul.hSMul, SMul.smul]
    refine Prod.ext ?_ ?_
    · have h1 := one_smul (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) p0.1.1
      simp only [HSMul.hSMul, SMul.smul] at h1
      exact h.trans h1.symm
    · funext P
      simp only [DecoF.fr, OneMemClass.coe_one, one_mul, InvMemClass.coe_inv, _root_.mul_inv_rev, inv_inv,
        ← mul_assoc, mul_inv_cancel]

variable (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)

theorem frm_root (hroot : ∀ c : ↥Θ.grp, ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : X.Kˣ) : X.K) ^ m = 1) (g : FrmG Λ Θ) :
    ∃ m : ℕ, 0 < m ∧ (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) ^ m = 1 := by
  haveI : ∀ w : SG, Finite (𝓞 X.E ⧸ w.1.asIdeal) := fun w =>
    Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  obtain ⟨m2, hm2, h2⟩ := hroot g.2.2
  have hfo : IsOfFinOrder g.2.1 := isOfFinOrder_of_finite _
  have ha : ((Λ.chr g.2.1 : X.Kˣ) : X.K) ^ orderOf g.2.1 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  refine ⟨orderOf g.2.1 * m2, Nat.mul_pos hfo.orderOf_pos hm2, ?_⟩
  rw [Units.val_mul, mul_pow, pow_mul, ha, one_pow, one_mul, mul_comm (orderOf _) m2, pow_mul, h2,
    one_pow]


open Classical in
theorem frmGSD_ok_of_finIdx (hX : X.Ok) (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (hC : C.Eqv)
    (hfi : ∀ P : Q, Finite (↥(GLint X.E n P.1) ⧸ (Θ P).H))
    (hroot : ∀ c : ↥Θ.grp, ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : X.Kˣ) : X.K) ^ m = 1) : (frmGSD (C.pull DecoF.deco) Λ Θ).Ok := by
  refine { fin_orb := ?_, fin_stab := ?_, nab_smul := ?_, del_smul := ?_, inv := ?_ }
  · obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have : Finite s := hs

    let pt : s → (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H) → Option (DecoF X.E n ST SG Q) := fun d cb =>
      if h : ∃ p0 : DecoF X.E n ST SG Q, p0.deco = d.1 then
        some (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • h.choose) else none
    have hfin : Finite (Option (s × (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H))) := inferInstance
    by_cases hne : Nonempty (frmGSD (C.pull DecoF.deco) Λ Θ).Cl
    swap
    · have := not_nonempty_iff.1 hne
      exact inferInstance
    obtain ⟨c00⟩ := hne
    refine Finite.of_surjective (fun a : s × (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H) =>
      match pt a.1 a.2 with
      | some p => (frmGSD (C.pull DecoF.deco) Λ Θ).cls p
      | none => c00) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h p =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep (DecoF.deco p)

      let p1 : DecoF X.E n ST SG Q := ((g, 1, 1) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q)⁻¹ • p
      have hp1 : p1.deco = d0 := by
        show ((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG))⁻¹ • p.deco = d0
        rw [hg, inv_smul_smul]
      have hex : ∃ p0 : DecoF X.E n ST SG Q, p0.deco = d0 := ⟨p1, hp1⟩
      obtain ⟨c, hc⟩ := frm_exists_c p1 hex.choose (hp1.trans hex.choose_spec.symm)

      let cb : ∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H := fun P => QuotientGroup.mk ((c P)⁻¹)
      have hout : ∀ P : Q, ((c P)⁻¹)⁻¹ * (cb P).out ∈ (Θ P).H := fun P => QuotientGroup.eq.1 (QuotientGroup.out_eq' (cb P)).symm
      refine ⟨(⟨d0, hd0⟩, cb), ?_⟩
      have hpt : pt ⟨d0, hd0⟩ cb = some (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • hex.choose) := dif_pos hex
      show (match pt ⟨d0, hd0⟩ cb with
        | some p => (frmGSD (C.pull DecoF.deco) Λ Θ).cls p
        | none => c00) = _
      rw [hpt]
      let θ : ↥Θ.grp := ⟨fun P => ((c P)⁻¹)⁻¹ * (cb P).out, fun P _ => hout P⟩
      refine ((frmGSD (C.pull DecoF.deco) Λ Θ).cls_eq_iff _ p).mpr ⟨((g, 1, θ) : FrmG Λ Θ)⁻¹, ?_⟩
      refine inv_smul_eq_iff.2 (Eq.symm ?_)
      show ((g, (1 : GLG (E := X.E) (n := n) (SG := SG)), (θ : GLQ X.E n Q)) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) •
        (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • hex.choose) = p
      rw [← mul_smul]
      have e : ((g, (1 : GLG (E := X.E) (n := n) (SG := SG)), (θ : GLQ X.E n Q)) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) * (1, 1, fun P => ((cb P).out)⁻¹) =
          (g, 1, 1) * (1, 1, c) := by
        refine Prod.ext (by simp) (Prod.ext (by simp) ?_)
        funext P
        show ((c P)⁻¹)⁻¹ * (cb P).out * ((cb P).out)⁻¹ = 1 * c P
        group
      rw [e, mul_smul, ← hc]
      exact smul_inv_smul _ p
  · intro p
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (DecoF.deco p : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (frmGSD (C.pull DecoF.deco) Λ Θ).G p =>
        (⟨(a.1.1, (a.1.2.1 : GLG (E := X.E) (n := n) (SG := SG))), congrArg DecoF.deco a.2⟩ :
          MulAction.stabilizer (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) (DecoF.deco p : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)))) ?_
    intro a b hab
    have h0 : ((a.1.1, (a.1.2.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) = (b.1.1, (b.1.2.1 : GLG (E := X.E) (n := n) (SG := SG))) :=
      congrArg Subtype.val hab
    exact Subtype.ext (dga_frm_stab_inj Λ Θ p a.2 b.2 (Prod.mk.inj h0).1)
  · intro g d
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    exact (hC.nab_smul (g.1, (g.2.1 : GLG (E := X.E) (n := n) (SG := SG))) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  · intro g d
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    exact (hC.del_smul (g.1, (g.2.1 : GLG (E := X.E) (n := n) (SG := SG))) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  · intro g (x : C.V) (y : C.V)
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    show C.pair ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 x)
      ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv, smul_smul]
    show (star (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

end Gen

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem chF_ok_of_finIdx (hX : X.Ok) (u : Pr.Word) (j : ℕ)
    (hfi : ∀ (b : L.β j) (P : QE sel (mu : Chr X.F X.E X.K)), Finite (↥(GLint X.E (R.N j) P.1) ⧸ (L.levQ j b P).H))
    (hroot : ∀ (b : L.β j) (c : ↥(L.levQ j b).grp), ∃ m : ℕ, 0 < m ∧ (((L.levQ j b).chr c : X.Kˣ) : X.K) ^ m = 1) :
    (chF W sel mu L u j).Ok := by
  intro b
  have hC : (colVal W u j (Pr.vT u) Pr.vGs).Eqv :=
    ⟨colVal_nab_smul W u j, colVal_del_smul W u j, roundPk_inv X _ _ hX.emb_star⟩
  exact frmGSD_ok_of_finIdx (L.levG j b) (L.levQ j b) hX (colVal W u j (Pr.vT u) Pr.vGs)
    hC (hfi b) (hroot b)

end Chain

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.CyclotomicIsCyclotomicExtension
section
open NumberField IsDedekindDomain Module IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Host Formalism.FrobeniusOrbits

section SplitGen

open Ideal

variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L]

end SplitGen

theorem cyclotomic_mono_of_dvd {M N : ℕ} (h : M ∣ N) : cycQ M ≤ cycQ N := by
  unfold cycQ
  apply adjoin.mono
  intro z hz
  obtain ⟨c, rfl⟩ := h
  show z ^ (M * c) = 1
  rw [pow_mul, show z ^ M = 1 from hz, one_pow]

section Split

variable {X : Fields}

end Split

section HostZ

variable {φ₁ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ₁) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : H.EQ ≤ LL)

def hwQb (d : ℕ) : Qb := Classical.choose (exists_sqrt (-(d : ℤ)))

theorem hwQb_mem (d : ℕ) : hwQb d ∈ sqrts (-(d : ℤ)) := Classical.choose_spec (exists_sqrt (-(d : ℤ)))

theorem hwQb_sq (d : ℕ) : hwQb d ^ 2 = -(d : Qb) := by
  have h : hwQb d ^ 2 = ((-(d : ℤ) : ℤ) : Qb) := hwQb_mem d
  rw [h]; simp

theorem hwQb_mem_EQ : hwQb H.d ∈ H.EQ :=
  H.KQ_le_EQ (sqrts_sub _ (hwQb_mem H.d))

def hwE : (hostFields H ι LL hE).E := (⟨hwQb H.d, hwQb_mem_EQ H⟩ : H.EQ)

theorem hwE_sq : hwE H ι LL hE ^ 2 = -(H.d : (hostFields H ι LL hE).E) := by
  have h : ((⟨hwQb H.d, hwQb_mem_EQ H⟩ : H.EQ)) ^ 2 = -(H.d : H.EQ) := Subtype.val_injective (by
    show hwQb H.d ^ 2 = _
    rw [hwQb_sq]
    simp)
  exact h

def hwO : 𝓞 (hostFields H ι LL hE).E :=
  ⟨hwE H ι LL hE, IsIntegral.of_pow (n := 2) (by norm_num) (by rw [hwE_sq]; exact (isIntegral_natCast H.d).neg)⟩

def hz (a b : ℤ) : 𝓞 (hostFields H ι LL hE).E :=
  (a : 𝓞 (hostFields H ι LL hE).E) + (b : 𝓞 (hostFields H ι LL hE).E) * hwO H ι LL hE

end HostZ

def toyFirstParameter : ℕ := 5812161310401002497

def toySecondParameter : ℕ := 10580716767734447210497

def nd2T : ℕ := 56194698826333161291662198507648755438473557111144279252246328293211974734191775333427954228508737780869538570051953955243454133837703637171933755744705457828859522702609327843686445057

def columnDegreeBound : ℕ := 175899382716746995995794692370095808443505986460327359316203003947391329197558870718244898147225575657278023097973275990081581282841096000378419862656504066221696375796925055794734493697

section CharsGen

variable {X : Fields}

variable {Pr : Primes X}

end CharsGen

section Hecke

variable {X : Fields} {Pr : Primes X} {R : Ranks}


end Hecke

def nd2N : ℕ := 204572886511813553061037407562329625995783655411690436542768105489192394035355663504895707466548678171695054788500010062488923813826764064938234928730947196464262768270018653110228498338042697795156970159903677022807129186961004810571117527615229822789011462114279289419559348825463524785325415815445950503458435921145728668675289394505621558664460319354973532563002004291054537384997546176343222140701606270894674242774158138205418672187221164903157007908864

open Formalism.BasicNotions.Examples₂ (H0)

theorem exampleField_le_cyclotomic : H0.EQ ≤ cycQ nd2N :=
  (condEQ H0).1.trans (cyclotomic_mono_of_dvd (by decide +kernel))

section Inst

variable (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hLL : cycQ nd2N ≤ LL)

abbrev nd2X : Fields := hostFields H0.toHostRaw ndIota LL (exampleField_le_cyclotomic.trans hLL)

abbrev nd2z (a b : ℤ) : 𝓞 (nd2X LL hLL).E := hz H0.toHostRaw ndIota LL (exampleField_le_cyclotomic.trans hLL) a b

def toyPrimes : Primes (nd2X LL hLL) where
  cond := H0.condN
  g := ![toyFirstParameter, toySecondParameter]
  piG := ![nd2z LL hLL 1 (((H0.condN : ℕ) : ℤ) * 18),
    nd2z LL hLL 1 (((H0.condN : ℕ) : ℤ) * 768)]
  Word := Fin 2
  T := ![nd2T, columnDegreeBound]
  piT := ![nd2z LL hLL 1 (((H0.condN * (toyFirstParameter * toySecondParameter) ^ 2 : ℕ) : ℤ) * 468),
    nd2z LL hLL 1 (((H0.condN * (toyFirstParameter * toySecondParameter) ^ 2 : ℕ) : ℤ) * 828)]

end Inst

section Gen

open ComplexOrder

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Gen


section Inst

variable (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hLL : cycQ nd2N ≤ LL)


end Inst

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.SummandSlopeOfThreeLemmas
section
open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality

section Defs

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

@[reducible] def latK (M : Submodule (𝓞 K) (Fin n → K)) : HLat K :=
  ofFormB (Pi.basisFun K (Fin n)) M (formAt (Pi.basisFun K (Fin n)) (hStd K n))

end Defs

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end

