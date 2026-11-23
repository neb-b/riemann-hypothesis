module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrimitiveCharacterMatchesLinesDownFlag
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.FlagDown

variable {D : D7}

theorem col_ne_zero {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (j : Fin ρ) : (fun k => d.e k j) ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun d.e'e j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have : ∀ k, d.e k j = 0 := fun k => congrFun h k
  simp [this] at h1

theorem colMul_eq {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (j : Fin ρ) (a : AE D) :
    colMul d.jX j a = a • ratV (fun k => d.e k j) := rfl

theorem mem_idAt_of_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (j : Fin ρ) {L : Lat S}
    {P : GlobalTheory.FinPl.Pl D → Prop} {a : AE D} (h : colMul d.jX j a ∈ latV S L P) : a ∈ idAt D P := by
  obtain ⟨k, hk⟩ : ∃ k, d.e k j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact col_ne_zero d j (funext hc)
  have h1 : a * incA D (d.e k j) ∈ idAt D P := GlobalTheory.FinPlLoc.latV_idAt h k
  have h2 := (idAt D P).mul_mem_right (incA D (d.e k j)⁻¹) h1
  rwa [mul_assoc, ← map_mul, mul_inv_cancel₀ hk, map_one, mul_one] at h2

theorem line_gen {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (j : Fin ρ) (L : Lat S) (hL : IsSelfDualC S L)
    (v : GlobalTheory.FinPl.Pl D) : ∃ x : D.host.E, x ≠ 0 ∧ ∀ a ∈ idAt D (· = v),
      (colMul d.jX j a ∈ latV S L (· = v) ↔ incA D x⁻¹ * a ∈ intAt D (· = v)) := by
  obtain ⟨𝔞, h𝔞, -, hv⟩ := _root_.GlobalTheory.Core.Mi.LatLine.line_trace D S L _ hL (col_ne_zero d j)
  obtain ⟨x, hx, hx'⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞 h𝔞
  refine ⟨x, hx, fun a ha => ?_⟩
  rw [colMul_eq, hv v a ha, hx']
  exact ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩

theorem cancel {v : GlobalTheory.FinPl.Pl D} (x : D.host.E) (hx : x ≠ 0) (P Q : AE D → Prop)
    (hP : ∀ o ∈ intAt D (· = v), ∀ t, P t → P (o * t)) (hQ : ∀ o ∈ intAt D (· = v), ∀ t, Q t → Q (o * t))
    (h : ∀ s ∈ idAt D (· = v),
      (∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) → P (s * a)) ↔
        (∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) → Q (s * a))) :
    ∀ t ∈ idAt D (· = v), P t ↔ Q t := by
  obtain ⟨ε, -, -, hε, hεid, -⟩ := GlobalTheory.FinPlLoc.part_idem (D := D) (· = v)
  intro t ht
  have hs : incA D x⁻¹ * t ∈ idAt D (· = v) := (idAt D _).mul_mem_left _ ht
  have ha0 : incA D x * ε ∈ idAt D (· = v) := (idAt D _).mul_mem_left _ hε.1
  have ha0' : incA D x⁻¹ * (incA D x * ε) ∈ intAt D (· = v) := by
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]
  have key : incA D x⁻¹ * t * (incA D x * ε) = t := by
    calc _ = (incA D x⁻¹ * incA D x) * (ε * t) := by ring
    _ = t := by rw [← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]; exact (hεid t).1 ht
  have red : ∀ R : AE D → Prop, (∀ o ∈ intAt D (· = v), ∀ t, R t → R (o * t)) → R t →
      ∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) → R (incA D x⁻¹ * t * a) := by
    intro R hR hRt a _ ha
    have := hR _ ha t hRt
    rwa [show incA D x⁻¹ * a * t = incA D x⁻¹ * t * a by ring] at this
  constructor
  · intro hPt
    have := (h _ hs).1 (red P hP hPt) _ ha0 ha0'
    rwa [key] at this
  · intro hQt
    have := (h _ hs).2 (red Q hQ hQt) _ ha0 ha0'
    rwa [key] at this

end GlobalTheory.Core.Mi.LatMatch.FlagDown


open GlobalTheory.Core.Mi.LatMatch.FlagDown in
theorem GlobalTheory.Core.Mi.LatMatch.match_down_flag : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L L' : Lat S) (v : GlobalTheory.FinPl.Pl D) (c : AE D), IsSelfDualC S L → PrimAt ψ d L v → PrimAt ψ d L' v → NormOneAt v c → ∀ i j : Fin ρ, j.1 = i.1 + 1 → (∀ a ∈ idAt D (· = v), (colMul d.jX j a ∈ latV S L (· = v) ↔ colMul d.jX j (c * a) ∈ latV S L' (· = v))) → ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) := by
  intro D ψ S S₀ ρ d L L' v c hsd hP hP' hc i j hij hj
  obtain ⟨x, hx, hA⟩ := line_gen d j L hsd v
  refine cancel x hx (fun t => colMul d.jX i t ∈ latV S L (· = v))
    (fun t => colMul d.jX i (c * t) ∈ latV S L' (· = v)) ?_ ?_ ?_
  · intro o ho t ht
    have e : colMul d.jX i (o * t) = o • colMul d.jX i t := by
      funext k; simp only [colMul, Pi.smul_apply, smul_eq_mul]; ring
    show colMul d.jX i (o * t) ∈ latV S L (· = v)
    rw [e]; exact GlobalTheory.FinPlLoc.smul_latV v ho ht
  · intro o ho t ht
    have e : colMul d.jX i (c * (o * t)) = o • colMul d.jX i (c * t) := by
      funext k; simp only [colMul, Pi.smul_apply, smul_eq_mul]; ring
    show colMul d.jX i (c * (o * t)) ∈ latV S L' (· = v)
    rw [e]; exact GlobalTheory.FinPlLoc.smul_latV v ho ht
  · intro s hs
    have e1 := hP i j hij s hs
    have e2 := hP' i j hij s hs
    have l1 : (∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) → colMul d.jX i (s * a) ∈ latV S L (· = v)) ↔
        (∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (s * a) ∈ latV S L (· = v)) := by
      constructor
      · intro H a ha
        have hid := mem_idAt_of_colMul d j ha
        exact H a hid ((hA a hid).1 ha)
      · intro H a ha hx'
        exact H a ((hA a ha).2 hx')
    have l2 : (∀ a ∈ idAt D (· = v), incA D x⁻¹ * a ∈ intAt D (· = v) →
        colMul d.jX i (c * (s * a)) ∈ latV S L' (· = v)) ↔
        (∀ a' : AE D, colMul d.jX j a' ∈ latV S L' (· = v) → colMul d.jX i (s * a') ∈ latV S L' (· = v)) := by
      constructor
      · intro H a' ha'
        have ha'id := mem_idAt_of_colMul d j ha'
        have hb : cA D c * a' ∈ idAt D (· = v) := (idAt D _).mul_mem_left _ ha'id
        have hcb : c * (cA D c * a') = a' := by rw [← mul_assoc, hc.1, one_mul]
        have hj' := (hj _ hb).2 (by rw [hcb]; exact ha')
        have := H _ hb ((hA _ hb).1 hj')
        rwa [show c * (s * (cA D c * a')) = s * (c * (cA D c * a')) by ring, hcb] at this
      · intro H a ha hx'
        have hj' := (hj a ha).1 ((hA a ha).2 hx')
        have := H _ hj'
        rwa [show s * (c * a) = c * (s * a) by ring] at this
    exact l1.trans (e1.trans e2.symm) |>.trans l2.symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PutInSplitPlacesDatumProductOnHalf
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PutIn

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem overAll_cons_iff (ψ : AddChar (AF D.host.F) ℂ) {p : ι → SplitPt D k} {S T : HSp D} (α : ∀ i, Frame (p i) S n')
    (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T) (Ψ : ι → Matrix n n' k → ℂ) (i : ι) (J : List ι) (f f' : WO S T → ℂ) :
    OverAll ψ α β LS LT Ψ (i :: J) f f' ↔ ∃ g, OverAll ψ α β LS LT Ψ J f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' := Iff.rfl

theorem sb_of_overAll (ψ : AddChar (AF D.host.F) ℂ) {p : ι → SplitPt D k} {S T : HSp D} (α : ∀ i, Frame (p i) S n')
    (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T) (Ψ : ι → Matrix n n' k → ℂ) (f : WO S T → ℂ) :
    ∀ (J : List ι) (f' : WO S T → ℂ), OverAll ψ α β LS LT Ψ J f f' → ∀ i ∈ J, Ψ i ∈ SB (Matrix n n' k) := by
  intro J
  induction J with
  | nil => intro _ _ i hi; simp at hi
  | cons j J ih =>
    intro f' h i hi
    obtain ⟨g, hg, hO⟩ := (overAll_cons_iff ψ α β LS LT Ψ j J f f').1 h
    rcases List.mem_cons.1 hi with rfl | hi
    · exact hO.2.2.2.1
    · exact ih g hg i hi

theorem mem_latO_at_iff (p : SplitPt D k) {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (t : WO S T) (ht : IsHalf p.e t) : t ∈ latO S T LS LT (· = p.v) ↔ t ∈ latO S T LS LT fun _ => True := by
  constructor
  · intro h; exact GlobalTheory.PlaceModel.latO_le_top _ h
  · intro h
    obtain ⟨ε, hε, hsum⟩ := p.above
    have he : p.e * p.e = p.e := p.split.1
    have hεe : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum, add_mul, he, mul_comm (cA D p.e), p.split.2.1, add_zero]
    have h1 := (GlobalTheory.PlaceModel.idem_smul_mem hε he hεe h).1
    have ht' : p.e • t = t := Matrix.ext fun i j => ht i j
    rwa [ht'] at h1

theorem isSBHalf_of_half_iff {S T : HSp D} (e : AE D) (Λ Λ' : AddSubgroup (WO S T)) (Φ : WO S T → ℂ)
    (hcmp : ∀ t, IsHalf e t → (t ∈ Λ' ↔ t ∈ Λ)) (h : IsSBHalf e Λ' Φ) : IsSBHalf e Λ Φ := by
  obtain ⟨hs, K, hK, hinv, hsup⟩ := h
  refine ⟨hs, K, hK, fun u hu hh t => hinv u ((hcmp u hh).2 hu) hh t, fun t ht => (hcmp _ ?_).1 (hsup t ht)⟩
  intro i j
  rw [Matrix.smul_apply, nsmul_eq_mul, ← mul_assoc, mul_comm e, mul_assoc, hs t ht i j]

open Classical in
theorem datJ_nil (p : ι → SplitPt D k) {S T : HSp D} (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n)
    (Ψ : ι → Matrix n n' k → ℂ) (Λ : AddSubgroup (WO S T)) : datJ p α β Ψ [] = halfInd 0 Λ := by
  funext t
  have h0 : IsHalf (0 : AE D) t → t ∈ Λ := fun ht => by
    have : t = 0 := Matrix.ext fun i j => by simpa [eq_comm] using ht i j
    rw [this]; exact zero_mem _
  unfold datJ halfInd
  by_cases ht : IsHalf (0 : AE D) t
  · rw [if_pos (by simpa [eSum] using ht), if_pos ⟨h0 ht, ht⟩]; rfl
  · rw [if_neg (by simpa [eSum] using ht), if_neg fun h => ht h.2]

theorem datJ_SB (p : ι → SplitPt D k) {S T : HSp D} (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n)
    (Ψ : ι → Matrix n n' k → ℂ) (LS : Lat S) (LT : Lat T) (hSD : IsSelfDualC S LS) (hTD : IsSelfDualC T LT)
    (horth : ∀ i j, i ≠ j → (p i).e * (p j).e = 0) :
    ∀ J : List ι, J.Nodup → (∀ i ∈ J, Ψ i ∈ SB (Matrix n n' k)) →
      IsSBHalf (eSum p J) (latO S T (LS : Set _) (LT : Set _) fun _ => True) (datJ p α β Ψ J) := by
  intro J
  induction J with
  | nil => intro _ _; rw [datJ_nil p α β Ψ (latO S T (LS : Set _) (LT : Set _) fun _ => True)]; exact GlobalTheory.isSBHalf_halfInd _ _
  | cons i J ih =>
    intro hJ hSB
    rw [List.nodup_cons] at hJ
    have hort : ∀ j ∈ J, (p i).e * (p j).e = 0 := fun j hj => horth i j fun h => hJ.1 (h ▸ hj)
    rw [_root_.GlobalTheory.FinPl.PutIn.datJ_cons D k ι p n n' S T α β Ψ i J hJ.1 hort, eSum_cons, add_comm]
    refine _root_.GlobalTheory.FinPl.PutIn.isSBHalf_tens D S T _ _ _ _ _ (eSum_mul p _ J fun j hj => by rw [mul_comm]; exact hort j hj) (p i).split.1
      (fun u hu => GlobalTheory.PlaceModelSum.idem_smul_latO (p i).split.1 hu) (ih hJ.2 fun j hj => hSB j (List.mem_cons_of_mem _ hj)) ?_
    exact isSBHalf_of_half_iff _ _ _ _ (fun t ht => mem_latO_at_iff (p i) _ _ t ht)
      (SBHalfAt.isSBHalf_extFun_latO D k (p i) S T n n' (α i) (β i) LS LT hSD hTD (Ψ i) (hSB i List.mem_cons_self))

theorem overAll_eq (ψ : AddChar (AF D.host.F) ℂ) (p : ι → SplitPt D k) {S T : HSp D} (α : ∀ i, Frame (p i) S n')
    (β : ∀ i, Frame (p i) T n) (Ψ : ι → Matrix n n' k → ℂ) (LS : Lat S) (LT : Lat T) (hSD : IsSelfDualC S LS)
    (hTD : IsSelfDualC T LT) (horth : ∀ i j, i ≠ j → (p i).e * (p j).e = 0) (f : WO S T → ℂ) :
    ∀ J : List ι, J.Nodup → ∀ (f' : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
      IsPlaceModel ψ (symplO S T) (heisO ψ S T) (eSum p J) (latO S T (LS : Set _) (LT : Set _) fun _ => True) 1 f Tm →
      OverAll ψ α β LS LT Ψ J f f' → f' = Tm (datJ p α β Ψ J) := by
  intro J
  induction J with
  | nil =>
    intro _ f' Tm hTm h
    have h1 : f' = f := h
    rw [h1, datJ_nil p α β Ψ (latO S T (LS : Set _) (LT : Set _) fun _ => True), ← hTm.vac, one_smul]
    rfl
  | cons i J ih =>
    intro hJ f' Tm hTm h
    obtain ⟨g, hg, hO⟩ := (overAll_cons_iff ψ α β LS LT Ψ i J f f').1 h
    have hJ' := List.nodup_cons.1 hJ
    have hort : ∀ j ∈ J, (p i).e * (p j).e = 0 := fun j hj => horth i j fun h => hJ'.1 (h ▸ hj)
    have hmul : eSum p J * (p i).e = 0 := eSum_mul p _ J fun j hj => by rw [mul_comm]; exact hort j hj
    have hstab : ∀ u ∈ (latO S T (LS : Set _) (LT : Set _) fun _ => True), (p i).e • u ∈ (latO S T (LS : Set _) (LT : Set _) fun _ => True) :=
      fun u hu => GlobalTheory.PlaceModelSum.idem_smul_latO (p i).split.1 hu
    rw [eSum_cons, add_comm] at hTm
    have hA := _root_.GlobalTheory.FinPl.PutIn.isPlaceModel_tensHalf D ψ S T (eSum p J) (p i).e _ f Tm hmul (p i).split.1 hstab hTm
    have hg' : g = Tm (tens (p i).e (datJ p α β Ψ J) (halfInd (p i).e (latO S T (LS : Set _) (LT : Set _) fun _ => True))) :=
      ih hJ'.2 g _ hA hg
    have hSBJ := datJ_SB p α β Ψ LS LT hSD hTD horth J hJ'.2
      (sb_of_overAll ψ α β LS LT Ψ f J g hg)
    have hcmp : ∀ t, IsHalf (p i).e t → (t ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v) ↔
        t ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True) :=
      fun t ht => mem_latO_at_iff (p i) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) t ht
    have hB := GlobalTheory.T.place_model_restricted_tensor_fixed_half D ψ S T (eSum p J) (p i).e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v)) (datJ p α β Ψ J) f Tm
      hmul (p i).split.1 hstab hcmp hSBJ hTm
    rw [← hg'] at hB
    rw [hO.2.2.2.2.2 _ hB, LinearMap.comp_apply, tensR_apply, _root_.GlobalTheory.FinPl.PutIn.datJ_cons D k ι p n n' S T α β Ψ i J hJ'.1 hort]

theorem ratDatum_of_overAll : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (J : List ι), Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T),
    IsSelfDualC S LS → IsSelfDualC T LT → (∀ z, z ∈ LS ↔ z ∈ intVec D S.rank) → (∀ z, z ∈ LT ↔ z ∈ intVec D T.rank) →
    ∀ (Pset : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e Pset →
    (∃ eq : ι ≃ Pset, ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e (eq i).1) →
    ∀ (Ψ : ι → Matrix n n' k → ℂ) (f f' : WO S T → ℂ), IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (stdHom S T) f →
    OverAll ψ α β LS LT Ψ J f f' →
    IsRatDatum ψ S T e (fun γ => (J.map fun i => Ψ i (rd (α i) (β i) (γ.map (incA D)))).prod) f f' := by
  intro D k _ _ _ _ ι p J hPl n n' _ _ _ _ ψ hψ S T α β LS LT hSD hTD hLS hLT Pset e hIdem hEq Ψ f f' hθf hvac hOver
  obtain ⟨horth, rfl⟩ := _root_.GlobalTheory.FinPl.PutIn.orth_and_eq_eSum D k ι p J _ hPl Pset e hIdem hEq
  have hΛ : stdHom S T = latO S T (LS : Set _) (LT : Set _) (fun _ => True) := by
    have h1 : (LS : Set (Fin S.rank → D.host.E)) = intVec D S.rank := Set.ext hLS
    have h2 : (LT : Set (Fin T.rank → D.host.E)) = intVec D T.rank := Set.ext hLT
    rw [h1, h2]
  have hid := eSum_idem p horth J hPl.nodup
  unfold IsRatDatum
  rw [hΛ] at hvac ⊢
  refine ⟨datJ p α β Ψ J, datJ_SB p α β Ψ LS LT hSD hTD horth J hPl.nodup (sb_of_overAll ψ α β LS LT Ψ f J f' hOver), ?_, ?_⟩
  · intro γ
    have hh : IsHalf (eSum p J) (γ.map fun a => eSum p J * incA D a) := fun i j => by
      rw [Matrix.map_apply, ← mul_assoc, hid]
    unfold datJ
    rw [if_pos hh]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    congr 1
    unfold rd
    congr 2
    ext a b
    simp only [Matrix.map_apply, map_mul, pr_eSum p horth J hPl.nodup i hi, one_mul]
  · exact ⟨(GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hψ S T LS LT hSD hTD Pset _ hIdem f hθf hvac).1,
      fun Tm hTm => overAll_eq ψ p α β Ψ LS LT hSD hTD horth f J hPl.nodup f' Tm hTm hOver⟩

end GlobalTheory.FinPl.PutIn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepMove

section Lattices

open GlobalTheory.FinPl hiding Pl

variable {D : D7}

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem mt_mul₀ (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := rfl

theorem mt_one₀ (V : HSp D) : mt V 1 = 1 := rfl

theorem mt_mul_inv (V : HSp D) (g : GA D V) (y : Fin V.rank → AE D) : mt V g *ᵥ (mt V g⁻¹ *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← mt_mul₀, mul_inv_cancel, mt_one₀, Matrix.one_mulVec]

theorem mulVec_mem_idAt {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE D)) {P : GlobalTheory.FinPl.Pl D → Prop} {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ idAt D P) (i : Fin n) : (A *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem moves_inv {S : HSp D} {g : GA D S} {L M : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (h : Moves S g L M P) :
    Moves S g⁻¹ M L P := by
  intro y hy
  have e := h (mt S g⁻¹ *ᵥ y) (mulVec_mem_idAt _ hy)
  rw [mt_mul_inv] at e
  exact e.symm

theorem mulVec_mem_latA {S : HSp D} {g : GA D S} {L M : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (h : Moves S g L M P)
    {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) : mt S g *ᵥ z ∈ latA S M P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hy
    set y' : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hy'
    have hy'm : y' ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hsplit : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y' := by
      funext i
      simp only [hy', Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    exact smul_mem_latA ha ((h y' (GlobalTheory.FinPl.FrameLat.latV_supp hy'm)).1 hy'm)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem actO_eq (S T : HSp D) (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g h u = HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹) := rfl

theorem actO_mem_latO {S T : HSp D} {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D S} {h : GA D T}
    (hg : Moves S g Λ M P) (hh : Moves T h Λ' M' P) {u : WO S T}
    (hu : u ∈ latO S T (Λ : Set _) (Λ' : Set _) P) : actO S T g h u ∈ latO S T (M : Set _) (M' : Set _) P := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T Λ Λ' hΛ hΛ' P] at hu
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T M M' hM hM' P]
  obtain ⟨hmx, hmap⟩ := hu
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [actO_eq, Matrix.mul_apply]
    refine sum_mem fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hmx k l)
  · change (HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹)) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : mt S g⁻¹ *ᵥ y ∈ latV S Λ P :=
      (moves_inv hg y (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy
    exact mulVec_mem_latA hh (hmap _ h1)

theorem actO_actO_inv {S T : HSp D} (g : GA D S) (h : GA D T) (u : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
  rw [actO_eq, actO_eq, inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul₀, mul_inv_cancel, mt_one₀, Matrix.one_mul,
    Matrix.mul_assoc, ← mt_mul₀, mul_inv_cancel, mt_one₀, Matrix.mul_one]

end Lattices

section Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

theorem isHalf_actO (g : GA D S) (h : GA D T) {e : AE D} {u : WO S T} (hu : IsHalf e u) : IsHalf e (actO S T g h u) := by
  intro i j
  rw [actO_eq]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hu k l]
  ring

theorem vac_move (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T}
    (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M')
    {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D S} {h : GA D T} (hg : GlobalTheory.FinPl.Moves S g Λ M P) (hh : GlobalTheory.FinPl.Moves T h Λ' M' P)
    {f : WO S T → ℂ} (hf : GlobalTheory.FinPl.Vac ψ S T Λ Λ' P f) : GlobalTheory.FinPl.Vac ψ S T M M' P (om (g, h) f) := by
  have back : ∀ u : WO S T, actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := actO_actO_inv g h
  have mem : ∀ u ∈ latO S T (M : Set _) (M' : Set _) P, actO S T g⁻¹ h⁻¹ u ∈ latO S T (Λ : Set _) (Λ' : Set _) P :=
    fun u hu => actO_mem_latO hM hΛ hM' hΛ' (moves_inv hg) (moves_inv hh) hu
  refine ⟨hW.om_pres _ _ hf.1, fun u hu => ?_, fun e he u hu hh' => ?_⟩
  · have h1 := hf.2.1 _ (mem u hu)
    have h2 : (2 • actO S T g⁻¹ h⁻¹ u : WO S T) = actO S T g⁻¹ h⁻¹ (2 • u) := by
      rw [actO_eq, actO_eq, two_nsmul, two_nsmul, Matrix.mul_add, Matrix.add_mul]
    have h3 := hW.om_heis g h (actO S T g⁻¹ h⁻¹ (2 • u)) f hf.1
    rw [back, ← h2, h1] at h3
    exact h3.symm
  · have h1 := hf.2.2 e he _ (mem u hu) (isHalf_actO g⁻¹ h⁻¹ hh')
    have h3 := hW.om_heis g h (actO S T g⁻¹ h⁻¹ u) f hf.1
    rw [back, h1] at h3
    exact h3.symm

theorem vacO_ne_zero {sS sT LS LT} {f : WO S T → ℂ} (hf : IsVacO ψ θ S T sS sT LS LT f) : f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hall⟩ := hf.2.norm
  have := hall p hp
  simp [nrm2] at this

theorem om_ne_zero (p : GA D S × GA D T) {f : WO S T → ℂ} (hf : f ≠ 0) : om p f ≠ 0 := by
  intro h0
  apply hf
  have : om p⁻¹ (om p f) = f := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  rw [← this, h0, map_zero]

theorem gen (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T}
    (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M')
    {g : GA D S} {h : GA D T} (hgf : g ∈ GfC S) (hhf : h ∈ GfC T)
    (hg : GlobalTheory.FinPl.Moves S g Λ M fun _ => True) (hh : GlobalTheory.FinPl.Moves T h Λ' M' fun _ => True)
    {sS sT} (BS BT) {f : WO S T → ℂ} (hf : IsVacO ψ θ S T sS sT (Λ : Set _) (Λ' : Set _) f) :
    (∀ P, ∀ x ∈ GinfC S, ∀ x' ∈ GinfC T, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True)
      (om (x * g, x' * h) (pureTensorO ψ θ S T sS sT BS BT f P))) ∧
      om (g, h) (pureTensorO ψ θ S T sS sT BS BT f 1) ≠ 0 := by
  have hθ : IsInfFam θ := hf.2.inf
  refine ⟨fun P x hx x' hx' => ?_, ?_⟩
  · have hv : GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) (om (g, h) f) :=
      vac_move hW hΛ hM hΛ' hM' hg hh ⟨hf.2.theta, hf.2.lat⟩
    have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT g h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgf, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hhf, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgf, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hhf, Matrix.one_mul]) f hf.2.theta P
    have e1 : ((x * g, x' * h) : GA D S × GA D T) = (x, x') * (g, h) := rfl
    rw [e1, map_mul, Module.End.mul_apply, hfin.2]
    exact (GlobalTheory.FockComb.om_pureTensorO_comb D ψ θ S T χS χT om hθ hW sS sT BS BT 0 (om (g, h) f) 0 0
      (fun u hu => by simp at hu) hv.1 GlobalTheory.OrientedHeis.theta_zero 1 (one_mem _) 1 (one_mem _)
      (by rw [map_zero, zero_smul]) P x hx x' hx').2 M M' hv
  · rw [GlobalTheory.FiniteFock.pureTensorO_one]
    exact om_ne_zero _ (vacO_ne_zero hf)

end Gen

theorem fock_vac_moved : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j + 1 < D.R.m → ∀ (g : GA D (Yc D j)) (g' : GA D (Yc D (j + 1))), g ∈ GfC (Yc D j) → g' ∈ GfC (Yc D (j + 1)) → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → (∀ P, GlobalTheory.FinPl.Moves (Yc D j) g ((pk W).ΛY j) M P) → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g' ((pk W).ΛY (j + 1)) M' P) → (∀ P, ∀ x ∈ GinfC (Yc D j), ∀ x' ∈ GinfC (Yc D (j + 1)), GlobalTheory.FinPl.Vac (pk W).ψ (Yc D j) (Yc D (j + 1)) M M' (fun _ => True) ((pk W).ωY W.P.A3.A.μ0 j (x * g, x' * g') (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P))) ∧ (pk W).ωY W.P.A3.A.μ0 j (g, g') (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) 1) ≠ 0 := by
  intro D L hT Gi Gl Kc Yd cX ex W hW j hj g g' hg hg' M M' hM hM' hm hm'
  have hLev := hW.bot.hyp.2.2.2.1.lev
  have sd : ∀ i, i < D.R.m → IsSelfDualC (Yc D i) ((pk W).ΛY i) := fun i hi =>
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY i hi)
  exact gen (W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj) (sd j (by omega)) hM (sd (j + 1) hj) hM' hg hg' (hm _) (hm' _) _ _
    (W.Q.charW.base.chain.vY W.P.A3.A.μ0 j hj).1

end GlobalTheory.StepMove

end
end

