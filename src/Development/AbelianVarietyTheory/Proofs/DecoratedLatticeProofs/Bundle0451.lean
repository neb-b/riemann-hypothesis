module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastIsotropicLineHomothetyMatchesLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LastLine

variable {D : D7}

theorem cancel (v : GlobalTheory.FinPl.Pl D) (x : D.host.E) (hx : x ≠ 0) (A : AE D → Prop)
    (hA : ∀ a ∈ idAt D (· = v), A a ↔ incA D x⁻¹ * a ∈ intAt D (· = v)) (P Q : AE D → Prop)
    (hP : ∀ o ∈ intAt D (· = v), ∀ t, P t → P (o * t)) (hQ : ∀ o ∈ intAt D (· = v), ∀ t, Q t → Q (o * t))
    (h : ∀ s ∈ idAt D (· = v), (∀ a ∈ idAt D (· = v), A a → P (s * a)) ↔ (∀ a ∈ idAt D (· = v), A a → Q (s * a))) :
    ∀ t ∈ idAt D (· = v), (P t ↔ Q t) := by
  intro t ht
  obtain ⟨ε, -, hεI, hε⟩ := GlobalTheory.IwaPlace.LocSD.exists_idem (D := D) v
  have hs : incA D x⁻¹ * t ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ht
  have ha0 : incA D x * ε ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hεI.1
  have hA0 : A (incA D x * ε) := by
    rw [hA _ ha0, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]
    exact hεI
  have hst : incA D x⁻¹ * t * (incA D x * ε) = t := by
    rw [show incA D x⁻¹ * t * (incA D x * ε) = (incA D x⁻¹ * incA D x) * (ε * t) by ring, ← map_mul,
      inv_mul_cancel₀ hx, map_one, one_mul, hε t ht]
  have hsa : ∀ a, incA D x⁻¹ * t * a = (incA D x⁻¹ * a) * t := fun a => by ring
  constructor
  · intro hPt
    have := (h _ hs).1 (fun a ha hAa => by
      rw [hsa]; exact hP _ ((hA a ha).1 hAa) t hPt) _ ha0 hA0
    rwa [hst] at this
  · intro hQt
    have := (h _ hs).2 (fun a ha hAa => by
      rw [hsa]; exact hQ _ ((hA a ha).1 hAa) t hQt) _ ha0 hA0
    rwa [hst] at this

theorem colMul_mul {m n : ℕ} (X : Mx D m n) (i : Fin n) (o t : AE D) :
    colMul X i (o * t) = o • colMul X i t := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.Core.Mi.LastLine

end

noncomputable section

namespace GlobalTheory.Core.Mi.LastLine

variable {D : D7}

theorem lastLine_match : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D) (γ : GA D S₀), IsSelfDualC S₀ M → z ≠ 0 → LastAt ψ d z L M v → LastAt ψ d z L' M' v → NormOneAt v c → Formalism.L2.Theta.mt S₀ γ *ᵥ ratV z = ratV z → SMoves S₀ c γ M M' v → ∀ i : Fin ρ, i.1 + 1 = ρ → ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) := by
  intro D ψ S S₀ ρ d z L L' M M' v c γ hM hz hL hL' hc hγ hmv i hi a ha
  obtain ⟨𝔞, h𝔞, -, hline⟩ := _root_.GlobalTheory.Core.Mi.LatLine.line_trace D S₀ M z hM hz
  obtain ⟨x, hx, hgen⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞 h𝔞
  have hA : ∀ b ∈ idAt D (· = v), b • ratV z ∈ latV S₀ M (· = v) ↔ incA D x⁻¹ * b ∈ intAt D (· = v) :=
    fun b hb => (hline v b hb).trans ((hgen b).trans ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩)
  have hent : ∀ b ∈ idAt D (· = v), ∀ k, (b • ratV z) k ∈ idAt D (· = v) := fun b hb k => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hb
  have hmove : ∀ b ∈ idAt D (· = v),
      b • ratV z ∈ latV S₀ M (· = v) ↔ (c * b) • ratV z ∈ latV S₀ M' (· = v) := by
    intro b hb
    rw [hmv _ (hent b hb), Matrix.mulVec_smul, hγ, smul_smul]
  have hcc : c * cA D c = 1 := hc.1
  have key : ∀ s ∈ idAt D (· = v),
      (∀ b ∈ idAt D (· = v), b • ratV z ∈ latV S₀ M (· = v) → colMul d.jX i (s * b) ∈ latV S L (· = v)) ↔
        (∀ b ∈ idAt D (· = v), b • ratV z ∈ latV S₀ M (· = v) →
          colMul d.jX i (c * (s * b)) ∈ latV S L' (· = v)) := by
    intro s hs
    rw [hL i hi s hs, ← hL' i hi s hs]
    constructor
    · intro h b hb hbM
      rw [show c * (s * b) = s * (c * b) by ring]
      exact h _ (Ideal.mul_mem_left _ _ hb) ((hmove b hb).1 hbM)
    · intro h b' hb' hb'M
      have hb : cA D c * b' ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hb'
      have hcb : c * (cA D c * b') = b' := by rw [← mul_assoc, hcc, one_mul]
      have := h _ hb ((hmove _ hb).2 (by rw [hcb]; exact hb'M))
      rwa [show c * (s * (cA D c * b')) = s * (c * (cA D c * b')) by ring, hcb] at this
  exact cancel v x hx (fun b => b • ratV z ∈ latV S₀ M (· = v)) hA
    (fun t => colMul d.jX i t ∈ latV S L (· = v)) (fun t => colMul d.jX i (c * t) ∈ latV S L' (· = v))
    (fun o ho t ht => by
      show colMul d.jX i (o * t) ∈ latV S L (· = v)
      rw [colMul_mul]
      exact GlobalTheory.FinPlLoc.smul_latV v ho ht)
    (fun o ho t ht => by
      show colMul d.jX i (c * (o * t)) ∈ latV S L' (· = v)
      rw [mul_left_comm, colMul_mul]
      exact GlobalTheory.FinPlLoc.smul_latV v ho ht)
    key a ha

end GlobalTheory.Core.Mi.LastLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastRowInvFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.RowModPrime

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem row_of_smul_eq {n : ℕ} (Q : GlobalTheory.LatPair.Pair k (Fin n)) (b b' : Matrix (Fin n) (Fin n) k) (hbb' : b * b' = 1)
    (c : k) (r₀ : Fin n)
    (hQ : ∀ (x : Fin n → k) (a : 𝓀[k]), Q.HasVal x a ↔ ∃ y : Fin n → 𝒪[k], (∀ r, (y r : k) = (b *ᵥ x) r) ∧
      ∃ s : 𝒪[k], (s : k) = c ∧ a = residue 𝒪[k] (s * y r₀))
    (g : GL (Fin n) k) (s : 𝓀[k]ˣ) (hg : g • Q = s • Q) (m : Fin n) :
    ∃ t : 𝒪[k], (t : k) = (b * (g⁻¹).val * b') r₀ m ∧ residue 𝒪[k] t = if m = r₀ then (s : 𝓀[k]) else 0 := by
  obtain ⟨e, he⟩ := Q.exists_hasVal_one
  obtain ⟨y₀, -, sc, hsc, h1⟩ := (hQ e 1).1 he
  have hsc0 : residue 𝒪[k] sc ≠ 0 := by
    intro h
    rw [map_mul, h, zero_mul] at h1
    exact one_ne_zero h1
  let y : Fin n → 𝒪[k] := Pi.single m 1
  have hbx : b *ᵥ (b' *ᵥ Pi.single m 1) = Pi.single m 1 := by
    rw [Matrix.mulVec_mulVec, hbb', Matrix.one_mulVec]
  have hx : Q.HasVal (b' *ᵥ Pi.single m 1) (residue 𝒪[k] (sc * y r₀)) := by
    refine (hQ _ _).2 ⟨y, fun r => ?_, sc, hsc, rfl⟩
    rw [hbx]
    simp only [y, Pi.single_apply]
    split_ifs <;> simp
  have hx2 : (g • Q).HasVal (b' *ᵥ Pi.single m 1) ((s : 𝓀[k]) * residue 𝒪[k] (sc * y r₀)) := by
    rw [hg, GlobalTheory.LatPair.Pair.dia_hasVal, Units.inv_mul_cancel_left]
    exact hx
  have hx3 := GlobalTheory.LatPair.Pair.smul_hasVal.1 hx2
  obtain ⟨y', hy', sc', hsc', h3⟩ := (hQ _ _).1 hx3
  have hss : sc' = sc := Subtype.ext (hsc'.trans hsc.symm)
  rw [hss] at h3
  have hM : (b *ᵥ (g⁻¹ • (b' *ᵥ Pi.single m 1))) r₀ = (b * (g⁻¹).val * b') r₀ m := by
    change (b *ᵥ ((g⁻¹).val *ᵥ (b' *ᵥ Pi.single m 1))) r₀ = _
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  refine ⟨y' r₀, (hy' r₀).trans hM, ?_⟩
  rw [map_mul, map_mul] at h3
  have h4 : residue 𝒪[k] sc * residue 𝒪[k] (y' r₀) = residue 𝒪[k] sc * ((s : 𝓀[k]) * residue 𝒪[k] (y r₀)) := by
    rw [← h3]; ring
  have h5 := mul_left_cancel₀ hsc0 h4
  rw [h5]
  simp only [y, Pi.single_apply]
  by_cases h : m = r₀
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h]
    simp

end GlobalTheory.AdForm.RowModPrime

namespace GlobalTheory.AdForm.RowModPrime

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem resS_eq_rho {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt q.e P) (ρ : 𝓀[k] ≃+* (𝓞 D.host.E ⧸ P.asIdeal))
    (hρ : ∀ (x : 𝓞 D.host.E) (t : 𝒪[k]), (t : k) = q.pr (incA D (x : D.host.E)) →
      ρ (residue 𝒪[k] t) = Ideal.Quotient.mk P.asIdeal x)
    (a : Formalism.L2.Herm.intAf D.host.F D.host.E) (t : 𝒪[k]) (ht : (t : k) = q.prF he a.1) :
    Formalism.L2.DIV.resS D.host.F P a = ρ (residue 𝒪[k] t) := by
  obtain ⟨x, hx0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx (D := D) P.ne_bot a
  have hx : a - Formalism.L2.DIV.oToS D.host.F D.host.E x ∈ Formalism.L2.DIV.idS D.host.F P.asIdeal := hx0
  have h1 : Formalism.L2.DIV.resS D.host.F P a = Ideal.Quotient.mk P.asIdeal x := by
    rw [← Formalism.L2.DIV.resS_oToS (F := D.host.F) P x, ← sub_eq_zero, ← map_sub]
    exact GlobalTheory.FinPl.SplitPt.resS_eq_zero_of_mem hx
  have h2 := q.val_lt_of_mem_idS he hx
  have e1 : ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (incA D (x : D.host.E)) := rfl
  have e2 : ((a - Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      (a : EAf D) - ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
  rw [e2, map_sub, e1, GlobalTheory.FinPl.SplitPt.prF_toEAf, ← ht] at h2
  have hw : q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := by
    have ht1 : valuation k (t : k) ≤ 1 := (Valuation.mem_integer_iff _ _).1 t.2
    have e3 : q.pr (incA D (x : D.host.E)) = (t : k) - ((t : k) - q.pr (incA D (x : D.host.E))) := by ring
    rw [Valuation.mem_integer_iff, e3]
    exact (Valuation.map_sub _ _ _).trans (max_le ht1 h2.le)
  let tw : 𝒪[k] := ⟨_, hw⟩
  have h3 : residue 𝒪[k] t = residue 𝒪[k] tw := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 (by simpa [tw] using h2))
  rw [h1, h3, hρ x tw rfl]

end GlobalTheory.AdForm.RowModPrime


open GlobalTheory.AdForm.RowModPrime in
theorem GlobalTheory.AdForm.lastRow_inv_frame : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 → ∀ (ρ : 𝓀[k] ≃+* (𝓞 B.fields.E ⧸ v.1.asIdeal)), (∀ (x : 𝓞 B.fields.E) (t : 𝒪[k]), (t : k) = (p i).pr (incA (I.rec7 l Z) (x : B.fields.E)) → ρ (residue 𝒪[k] t) = Ideal.Quotient.mk v.1.asIdeal x) →
    ∀ (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (s : 𝓀[k]ˣ), g • Q j i = s • Q j i → ∀ δ : TC.GA B (B.R.N j), δ.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) →
      (∀ r r', (δ⁻¹).1 r r' ∈ Formalism.L2.DIV.RInt B.host.F B.host.E) →
      ∀ r r' : Fin (B.R.N j), r.1 + 1 = B.R.N j → HasRes v.1 (adAt B.host.F v.1 ((δ⁻¹).1 r r')) (if r' = r then ρ (s : 𝓀[k]) else 0) := by
  intro B X I hOk hP l Z u a k _ _ _ _ ι p β Q L hStd j hj i v hId ρ hρ g s hg δ hδ hint r r' hr
  have hn : ((I.rec7 l Z).sp.X j).rank = B.R.N j := rankN (I.rec7 l Z) j hj
  let e : Fin ((I.rec7 l Z).sp.X j).rank ≃ Fin (B.R.N j) := finCongr hn
  let f : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (EAf (I.rec7 l Z)) →+* Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) k :=
    ((p i).prF hId).mapMatrix
  have hδm : f δ.1 = Matrix.reindex e e ((β j i).b * g.val * (β j i).b') := by
    rw [hδ, ← (β j i).gl_mat g]
    ext x y
    exact GlobalTheory.FinPl.SplitPt.prF_toEAf (p i) hId _
  have hY : Matrix.reindex e e ((β j i).b * g.val * (β j i).b') * Matrix.reindex e e ((β j i).b * (g⁻¹).val * (β j i).b') = 1 := by
    rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    have : (β j i).b * g.val * (β j i).b' * ((β j i).b * (g⁻¹).val * (β j i).b') = 1 := by
      calc (β j i).b * g.val * (β j i).b' * ((β j i).b * (g⁻¹).val * (β j i).b')
          = (β j i).b * (g.val * ((β j i).b' * (β j i).b) * (g⁻¹).val) * (β j i).b' := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [(β j i).b'b, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, (β j i).bb']
    rw [this, Matrix.submatrix_one_equiv]
  have h1 : ((δ⁻¹).1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (EAf (I.rec7 l Z))) * δ.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hX : f (δ⁻¹).1 * f δ.1 = 1 :=
    (map_mul f _ _).symm.trans ((congrArg f h1).trans (map_one f))
  have hA : f (δ⁻¹).1 = Matrix.reindex e e ((β j i).b * (g⁻¹).val * (β j i).b') := by
    calc f (δ⁻¹).1 = f (δ⁻¹).1 * (f δ.1 * Matrix.reindex e e ((β j i).b * (g⁻¹).val * (β j i).b')) := by
          rw [hδm, hY, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hX, Matrix.one_mul]
  have hA' : (p i).prF hId ((δ⁻¹).1 r r') = ((β j i).b * (g⁻¹).val * (β j i).b') (e.symm r) (e.symm r') :=
    congrFun (congrFun hA r) r'
  have hr0 : (e.symm r).1 + 1 = ((I.rec7 l Z).sp.X j).rank := by
    show r.1 + 1 = _
    rw [hr]
    exact hn.symm
  have hQ := GlobalTheory.AdForm.stdT_pair_coords I l Z u k ι p β Q L hStd j hj i (e.symm r) hr0
  obtain ⟨t, ht, hres⟩ := row_of_smul_eq (Q j i) (β j i).b (β j i).b' (β j i).bb' _ (e.symm r) hQ g s hg (e.symm r')
  have hmem := hint r r'
  have h := GlobalTheory.Mem.Col2.PtExist.hasRes_redA v.1 hmem
  have hr1 : Formalism.L2.Col.redA v.1 ((δ⁻¹).1 r r') = ρ (residue 𝒪[k] t) :=
    (Formalism.L2.Col.redA_int v.1 hmem).trans (resS_eq_rho (p i) hId ρ hρ ⟨_, hmem⟩ t (ht.trans hA'.symm))
  rw [hr1, hres] at h
  convert h using 2
  by_cases h' : r' = r
  · subst h'; simp
  · rw [if_neg h', if_neg (fun h'' => h' (e.symm.injective h'')), map_zero]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeResiduePairEqScalarOfSameStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

noncomputable section

namespace GlobalTheory.LatPair.StabScal

section SlopeTestRemainingChoices
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]

def scal (s : k) (hs : s ≠ 0) : GL n k :=
  ⟨s • 1, s⁻¹ • 1, by rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hs, one_smul],
    by rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hs, one_smul]⟩

theorem scal_inv_smul (s : k) (hs : s ≠ 0) (x : n → k) : (scal s hs : GL n k)⁻¹ • x = s⁻¹ • x := by
  show (s⁻¹ • (1 : Matrix n n k)) *ᵥ x = _
  rw [Matrix.smul_mulVec, one_mulVec]

theorem scal_comm (s : k) (hs : s ≠ 0) (h : GL n k) : h * scal s hs = scal s hs * h := by
  ext1
  show h.val * (s • (1 : Matrix n n k)) = (s • (1 : Matrix n n k)) * h.val
  rw [mul_smul_comm, mul_one, smul_mul_assoc, one_mul]

def trv (b d : n) (t : k) (hbd : b ≠ d) : GL n k :=
  ⟨Matrix.transvection b d t, Matrix.transvection b d (-t),
   by rw [Matrix.transvection_mul_transvection_same b d hbd, add_neg_cancel, Matrix.transvection_zero],
   by rw [Matrix.transvection_mul_transvection_same b d hbd, neg_add_cancel, Matrix.transvection_zero]⟩

theorem transvection_mulVec' (b d : n) (t : k) (x : n → k) :
    Matrix.transvection b d t *ᵥ x = x + Pi.single b (t * x d) := by
  ext j
  simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.single_apply]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, ite_and]
  by_cases h : b = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem trv_inv_smul (b d : n) (t : k) (hbd : b ≠ d) (x : n → k) :
    (trv b d t hbd)⁻¹ • x = x + Pi.single b (-t * x d) := transvection_mulVec' b d (-t) x

end SlopeTestRemainingChoices

theorem transvection_smul_stdPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i b d : n) (t : 𝒪[k]) (g : GL n k), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → g.val = Matrix.transvection b d (t : k) → g • GlobalTheory.LatPair.stdPair k i = GlobalTheory.LatPair.stdPair k i := by
  intro k _ _ _ _ n _ _ i b d t g hbd hbi hg
  have hinv : (g⁻¹ : GL n k).val = Matrix.transvection b d (-(t : k)) := by
    have h1 : (g⁻¹ : GL n k).val * g.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (g⁻¹ : GL n k).val = (g⁻¹ : GL n k).val * (g.val * Matrix.transvection b d (-(t : k))) := by
          rw [hg, Matrix.transvection_mul_transvection_same b d hbd, add_neg_cancel, Matrix.transvection_zero,
            mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  have htO : (t : k) ∈ 𝒪[k] := t.2
  refine Pair.ext fun x a => ?_
  let y : n → k := x + Pi.single b (-(t : k) * x d)
  have hyj : ∀ j, y j = x j + (Pi.single b (-(t : k) * x d) : n → k) j := fun j => rfl
  have hsm : g⁻¹ • x = y := by
    show (g⁻¹ : GL n k).val *ᵥ x = _
    rw [hinv, transvection_mulVec']
  rw [Pair.smul_hasVal, hsm, stdPair_hasVal, stdPair_hasVal]
  have hd : y d = x d := by rw [hyj]; simp [Pi.single_apply, Ne.symm hbd]
  have hint : (∀ j, y j ∈ 𝒪[k]) ↔ ∀ j, x j ∈ 𝒪[k] := by
    constructor
    · intro hy j
      have hxd : x d ∈ 𝒪[k] := by rw [← hd]; exact hy d
      have : x j = y j + (Pi.single b ((t : k) * x d) : n → k) j := by
        rw [hyj]
        simp only [Pi.single_apply]
        split_ifs <;> ring
      rw [this]
      refine add_mem (hy j) ?_
      rw [Pi.single_apply]
      split_ifs
      · exact mul_mem htO hxd
      · exact zero_mem _
    · intro hx j
      rw [hyj, Pi.single_apply]
      split_ifs
      · exact add_mem (hx j) (mul_mem (neg_mem htO) (hx d))
      · simpa using hx j
  have hres : ∀ (hx : ∀ j, x j ∈ 𝒪[k]) (hy : ∀ j, y j ∈ 𝒪[k]),
      IsLocalRing.residue 𝒪[k] ⟨y i, hy i⟩ = IsLocalRing.residue 𝒪[k] ⟨x i, hx i⟩ := by
    intro hx hy
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    by_cases hb : b = i
    · subst hb
      have hm : t ∈ IsLocalRing.maximalIdeal 𝒪[k] := hbi.resolve_left (not_not.2 rfl)
      have : (⟨y b, hy b⟩ : 𝒪[k]) - ⟨x b, hx b⟩ = -(t * ⟨x d, hx d⟩) := by
        apply Subtype.ext
        push_cast
        rw [hyj, Pi.single_eq_same]
        ring
      rw [this]
      exact neg_mem (Ideal.mul_mem_right _ _ hm)
    · have : (⟨y i, hy i⟩ : 𝒪[k]) - ⟨x i, hx i⟩ = 0 := by
        apply Subtype.ext
        show y i - x i = 0
        rw [hyj]
        simp [Pi.single_apply, Ne.symm hb]
      rw [this]
      exact zero_mem _
  constructor
  · rintro ⟨hy, rfl⟩
    exact ⟨hint.1 hy, (hres _ hy).symm⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨hint.2 hx, hres hx _⟩

theorem eq_scalar_smul_of_stab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (P P' : GlobalTheory.LatPair.Pair k n), 3 ≤ Fintype.card n → (∀ g : GL n k, g • P = P ↔ g • P' = P') → ∃ (g : GL n k) (s : k), s ≠ 0 ∧ g.val = s • (1 : Matrix n n k) ∧ P' = g • P := by
  intro k _ _ _ _ n _ _ P P' hn hst
  obtain ⟨i⟩ : Nonempty n := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (GL n k) (stdPair k i) P
  set Q := h⁻¹ • P' with hQ
  clear_value Q
  have hstQ : ∀ g : GL n k, g • stdPair k i = stdPair k i → g • Q = Q := by
    intro g hg
    have h1 : (h * g * h⁻¹) • P = P := by rw [← hh, smul_smul, show h * g * h⁻¹ * h = h * g by group, mul_smul, hg]
    have h2 := (hst _).1 h1
    rw [hQ, smul_smul]
    calc (g * h⁻¹) • P' = h⁻¹ • (h * g * h⁻¹) • P' := by rw [smul_smul]; congr 1; group
      _ = h⁻¹ • P' := by rw [h2]
  have hcl : ∀ (x : n → k) (a : 𝓀[k]), Q.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d →
      (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → Q.HasVal (x + Pi.single b ((t : k) * x d)) a := by
    intro x a hx b d t hbd hbi
    have hg : trv b d ((-t : 𝒪[k]) : k) hbd • stdPair k i = stdPair k i :=
      transvection_smul_stdPair k n i b d (-t) _ hbd (hbi.imp id (fun h => (IsLocalRing.maximalIdeal 𝒪[k]).neg_mem_iff.2 h)) rfl
    have h2 : (trv b d ((-t : 𝒪[k]) : k) hbd • Q).HasVal x a := by rw [hstQ _ hg]; exact hx
    rw [Pair.smul_hasVal, trv_inv_smul] at h2
    convert h2 using 3
    push_cast
    ring
  have hlat : ∀ x ∈ Q.lat, ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) →
      x + Pi.single b ((t : k) * x d) ∈ Q.lat := fun x hx b d t hbd hbi =>
    (hcl x _ (Q.hasVal_fn ⟨x, hx⟩) b d t hbd hbi).mem
  have hbound : ∃ c : k, c ≠ 0 ∧ (∀ x ∈ Q.lat, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧
      ∃ x ∈ Q.lat, ∃ j, x j = c := by
    first
    | exact GlobalTheory.T.localLattice_exists_scalar_bound_attained k n Q.lat Q.isLat ⟨i⟩
    | exact GlobalTheory.T.localLattice_exists_scalar_bound_attained k n Q.lat Q.isLat.toIsLattice ⟨i⟩
  obtain ⟨c, hc0, hcb, hca⟩ := hbound
  rcases _root_.GlobalTheory.LatPairStab.stable_lattice_shape k n i Q.lat c hn hc0 hlat hcb hca with hA | hB
  swap
  · exact (_root_.GlobalTheory.LatPair.no_pair_on_scaled_kernel k n i Q c hn hc0 hB hcl).elim
  obtain ⟨ε, hε0, hε⟩ := _root_.GlobalTheory.latPair_hasVal_residue_of_transvections k n i Q c (by omega) hc0 hA hcl
  obtain ⟨w, hw⟩ := IsLocalRing.residue_surjective (R := 𝒪[k]) ε
  have hwu : IsUnit w := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, hw]
    exact hε0
  obtain ⟨u, hu⟩ := hwu
  have huw : (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) * (w : k) = 1 := by
    have h1 : ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) * w = 1 := by rw [← hu, Units.inv_mul]
    have h2 := congrArg (fun z : 𝒪[k] => (z : k)) h1
    simpa using h2
  have hw0 : (w : k) ≠ 0 := fun h0 => by simp [h0] at huw
  have hint : ∀ y : k, (w : k) * y ∈ 𝒪[k] → y ∈ 𝒪[k] := by
    intro y hy
    have : y = (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) * ((w : k) * y) := by rw [← mul_assoc, huw, one_mul]
    rw [this]
    exact mul_mem (u⁻¹ : 𝒪[k]ˣ).val.2 hy
  set s := c * (w : k)⁻¹ with hs_def
  have hs : s ≠ 0 := mul_ne_zero hc0 (inv_ne_zero hw0)
  have key : ∀ y : k, s⁻¹ * y = (w : k) * (c⁻¹ * y) := by
    intro y
    rw [hs_def, mul_inv, inv_inv]
    ring
  have hQs : Q = (scal s hs : GL n k) • stdPair k i := by
    refine Pair.ext fun x a => ?_
    rw [Pair.smul_hasVal, stdPair_hasVal, scal_inv_smul]
    constructor
    · intro hQx
      have hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k] := (hA x).1 hQx.mem
      refine ⟨fun j => ?_, ?_⟩
      · rw [Pi.smul_apply, smul_eq_mul, key]
        exact mul_mem w.2 (hx j)
      · rw [hQx.unique (hε x hx), ← hw, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Pi.smul_apply, smul_eq_mul, key]
        push_cast
        ring
    · rintro ⟨hx', rfl⟩
      have hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k] := fun j => hint _ (by have := hx' j; rwa [Pi.smul_apply, smul_eq_mul, key] at this)
      convert hε x hx using 1
      rw [← hw, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Pi.smul_apply, smul_eq_mul, key]
      push_cast
      ring
  refine ⟨(scal s hs : GL n k), s, hs, rfl, ?_⟩
  calc P' = h • Q := by rw [hQ, smul_inv_smul]
    _ = h • (scal s hs : GL n k) • stdPair k i := by rw [hQs]
    _ = (scal s hs : GL n k) • P := by rw [← hh, smul_smul, smul_smul, scal_comm]

end GlobalTheory.LatPair.StabScal

end
end

