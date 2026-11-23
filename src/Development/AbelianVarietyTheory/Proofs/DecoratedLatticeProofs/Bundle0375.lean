module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomSphericalCardWeightIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BottomWt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem relIndex_KO_ne_zero {n : Type} [Fintype n] [DecidableEq n] {J : Subgroup (GL n k)}
    (hJ : J ≤ KO k n) (ho : IsOpen (J : Set (GL n k))) : J.relIndex (KO k n) ≠ 0 := by
  haveI : CompactSpace (KO k n) := isCompact_iff_compactSpace.1 SplitFlip.isCompact_KO
  haveI : Finite ((KO k n) ⧸ J.subgroupOf (KO k n)) :=
    Subgroup.quotient_finite_of_isOpen _ (ho.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem N_one_apply_inl {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {u : GL (n ⊕ Fin c) k}
    (hu : u ∈ N k n c 1) (a b : n) : u.val (Sum.inl a) (Sum.inl b) = (1 : Matrix n n k) a b := by
  have := GlobalTheory.RootEx.prodN_inN_of_mem hu (Sum.inl a) (Sum.inl b) le_rfl
  simpa [Matrix.one_apply] using this

theorem mul_embX_inl {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {u : GL (n ⊕ Fin c) k}
    (hu : u ∈ N k n c 1) (g : GL n k) (a b : n) :
    (u * embX c g).val (Sum.inl a) (Sum.inl b) = g.val a b := by
  simp only [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, embX]
  simp [N_one_apply_inl hu, Matrix.one_apply]

theorem embX_mul_inl {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {u : GL (n ⊕ Fin c) k}
    (hu : u ∈ N k n c 1) (g : GL n k) (a b : n) :
    (embX c g * u).val (Sum.inl a) (Sum.inl b) = g.val a b := by
  simp only [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, embX]
  simp [N_one_apply_inl hu, Matrix.one_apply]

theorem intM_embX {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {g : GL n k} (h : IntM g.val) :
    IntM (embX c g : GL (n ⊕ Fin c) k).val := by
  rintro (a | a) (b | b)
  · simpa [embX] using h a b
  · simp [embX]
  · simp [embX]
  · by_cases e : a = b
    · subst e; simp [embX]
    · simp [embX, Matrix.one_apply, e]

theorem prX_Cgrp_KO_one (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) :
    prX (Cgrp (KO k (n ⊕ Fin c)) 1) = KO k n := by
  ext g
  rw [mem_prX]
  constructor
  · rintro ⟨u, hu, hC⟩
    have hw : u * embX c g ∈ KO k (n ⊕ Fin c) := by simpa using (mem_Cgrp.1 hC).2
    obtain ⟨h1, h2⟩ := mem_KO.1 hw
    refine mem_KO.2 ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [← mul_embX_inl hu g a b]; exact h1 _ _
    · have hu' : u⁻¹ ∈ N k n c 1 := inv_mem hu
      have e : (u * embX c g)⁻¹ = embX c g⁻¹ * u⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
      rw [← embX_mul_inl hu' g⁻¹ a b, ← e]; exact h2 _ _
  · intro hg
    refine ⟨1, one_mem _, ?_⟩
    rw [one_mul, mem_Cgrp]
    refine ⟨Subgroup.mem_sup_left ⟨g, rfl⟩, ?_⟩
    simp only [inv_one, one_mul, mul_one]
    obtain ⟨h1, h2⟩ := mem_KO.1 hg
    refine mem_KO.2 ⟨intM_embX h1, ?_⟩
    rw [← map_inv]; exact intM_embX h2

theorem reGL_symm_mem_KO_iff {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    {x : GL b k} : (reGL e).symm x ∈ KO k a ↔ x ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using h1 (e.symm i) (e.symm j)
    · simpa using h2 (e.symm i) (e.symm j)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

theorem twistChain_lev_zero {s : ℕ} {t κ : Type} [Fintype t] [DecidableEq t] [Fintype κ] [DecidableEq κ]
    (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (c : ℕ) (h : 0 + c = s + 1) :
    ((twistChain s t κ δ hδ η).lev 0 c h).J = KO k _ := by
  ext x
  change (plainFrame (k := k) (stdOrd κ t 0 c h)).conj.symm x ∈ (parahoric (κ ⊕ Fin (s + 1)) (Fin 0 × t) δ hδ).J ↔ _
  rw [mem_parahoric]
  have e : (plainFrame (k := k) (stdOrd κ t 0 c h)).conj.symm x = (reGL (stdOrd κ t 0 c h)).symm x := by
    simp [LatFrame.conj, plainFrame]
    rfl
  rw [e, reGL_symm_mem_KO_iff]
  exact ⟨fun H => H.1, fun H => ⟨H, fun i _ => i.1.elim0⟩⟩

end GlobalTheory.BottomWt

namespace GlobalTheory.QTw
open GlobalTheory.BottomWt

theorem QExt.bottom_one : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) (E : QExt G χ), Fintype.card (E.Ch 0) = 1 ∧ (∀ α, E.wt 0 α = 1) ∧ E.idx 0 = 1 ∧ ∀ j, j ≤ G.s + 1 + 1 → E.idx j ≠ 0 := by
  intro D c v B PP G χ E
  have hz : E.A 0 G.s (zero_add _) = {1} := E.reps.zero _ _
  have hrep : ∀ α, E.rep 0 G.s (zero_add _) α = 1 := fun α => by
    have := (E.rep_bij 0 G.s (zero_add _)).mapsTo (Set.mem_univ α)
    rw [hz] at this
    exact this
  have hJ0 : ∀ c h, ((G.T E.δ E.tame E.η).lev 0 c h).J = KO G.k _ := fun c h =>
    twistChain_lev_zero E.δ E.tame E.η c h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_eq_one_iff]
    have h1 : (1 : GL _ G.k) ∈ E.A 0 G.s (zero_add _) := by rw [hz]; rfl
    obtain ⟨x, -, -⟩ := (E.rep_bij 0 G.s (zero_add _)).surjOn h1
    exact ⟨x, fun y => (E.rep_bij 0 G.s (zero_add _)).injOn (Set.mem_univ _) (Set.mem_univ _)
      ((hrep y).trans (hrep x).symm)⟩
  · intro α
    rw [E.wt_mid 0 G.s (zero_add _) α, hrep α, hJ0, prX_Cgrp_KO_one, (E.haar 0).2]
    simp
  · rw [E.idx_mid 0 (G.s + 1) (zero_add _), hJ0]
    exact Subgroup.relIndex_self _
  · intro j hj
    rcases Nat.lt_or_ge j (G.s + 2) with hl | hl
    · rw [E.idx_mid j (G.s + 1 - j) (by omega)]
      exact relIndex_KO_ne_zero (E.le _ _ _) (E.reg.2.2 _ _ _).1
    · obtain rfl : j = G.s + 1 + 1 := by omega
      rw [E.idx_top]
      exact relIndex_KO_ne_zero E.leT E.openT

end GlobalTheory.QTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfEachPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.MovesPl

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit GlobalTheory.FinPl.KOpen

variable {D : D7}

theorem latV_transfer (S : HSp D) (L : Lat S) {P₁ P₂ : Pl D → Prop} (h : ∀ p, P₁ p → P₂ p)
    {z : Fin S.rank → AE D} (hz : ∀ i, z i ∈ idAt D P₁) : z ∈ latV S L P₁ ↔ z ∈ latV S L P₂ := by
  rw [mem_latV_iff S L P₁ z hz, mem_latV_iff S L P₂ z fun i => idAt_mono h (hz i)]

theorem mem_latV_empty (S : HSp D) (L : Lat S) {z : Fin S.rank → AE D}
    (hz : ∀ i, z i ∈ idAt D (· ∈ (∅ : Finset (Pl D)))) : z ∈ latV S L (· ∈ (∅ : Finset (Pl D))) := by
  classical
  rw [mem_latV_iff S L _ z hz]
  have h0 : finPart D ∘ z = 0 := by
    funext i
    rw [Function.comp_apply, ← e_mul_fin (hz i)]
    refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_
    change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w _ = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w _
    rw [map_mul, compFin_e, if_neg (Finset.notMem_empty w), zero_mul, Pi.zero_apply, map_zero]
  rw [h0]
  exact zero_mem _

theorem moves_of_places : ∀ {D : D7} (S : HSp D) (g : GA D S) (L M : Lat S) (Q : Finset (Pl D)),
    (∀ v ∈ Q, Moves S g L M (· = v)) → Moves S g L M (· ∈ Q) := by
  intro D S g L M Q
  classical
  induction Q using Finset.induction_on with
  | empty =>
    intro _ y hy
    exact iff_of_true (mem_latV_empty S L hy) (mem_latV_empty S M (supp_mulVec S _ g hy))
  | insert v Q hv ih =>
    intro hQ y hy
    have hQ' := ih fun w hw => hQ w (Finset.mem_insert_of_mem hw)
    have hvv := hQ v (Finset.mem_insert_self v Q)
    have hgy := supp_mulVec S _ g hy
    have comm : ∀ c : AE D, c • (mt S g *ᵥ y) = mt S g *ᵥ (c • y) := fun c => (mulVec_smul _ _ _).symm
    have s1 : ∀ i, (eQ {v} • y) i ∈ idAt D (fun p => p ∈ insert v Q ∧ p ∈ ({v} : Finset (Pl D))) :=
      fun i => mul_mem_idAt (eQ_off {v}) (hy i)
    have s2 : ∀ i, ((1 - eQ {v}) • y) i ∈ idAt D (fun p => p ∈ insert v Q ∧ p ∉ ({v} : Finset (Pl D))) :=
      fun i => mul_mem_idAt (one_sub_eQ_off {v}) (hy i)
    have i1 : ∀ p, (p ∈ insert v Q ∧ p ∈ ({v} : Finset (Pl D))) → p = v := fun p h => Finset.mem_singleton.1 h.2
    have i2 : ∀ p, (p ∈ insert v Q ∧ p ∉ ({v} : Finset (Pl D))) → p ∈ Q := fun p h =>
      (Finset.mem_insert.1 h.1).resolve_left fun e => h.2 (Finset.mem_singleton.2 e)
    have t1 : ∀ i, (eQ {v} • y) i ∈ idAt D (· = v) := fun i => idAt_mono i1 (s1 i)
    have t2 : ∀ i, ((1 - eQ {v}) • y) i ∈ idAt D (· ∈ Q) := fun i => idAt_mono i2 (s2 i)
    rw [mem_latV_iff_parts S L _ {v} hy, mem_latV_iff_parts S M _ {v} hgy, comm, comm,
      latV_transfer S L i1 s1, latV_transfer S L i2 s2,
      latV_transfer S M i1 (fun i => by rw [← comm]; exact mul_mem_idAt (eQ_off {v}) (hgy i)),
      latV_transfer S M i2 (fun i => by rw [← comm]; exact mul_mem_idAt (one_sub_eQ_off {v}) (hgy i))]
    exact and_congr (hvv _ t1) (hQ' _ t2)

end GlobalTheory.FinPl.MovesPl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOnOffIffAllFinitePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.MovesSplit

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit GlobalTheory.FinPlLoc

variable {D : D7}

theorem idem_eq_algebraMap (R : Pl D → Prop) :
    idem D R = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (ePl D R)) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rfl

theorem idem_smul_mem (S : HSp D) (L : Lat S) {P : Pl D → Prop} (R : Pl D → Prop) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : idem D R • y ∈ latV S L (fun p => P p ∧ R p) := by
  classical
  rw [idem_eq_algebraMap]
  exact smul_mem_latV S L (ePl D R) (ePl_int R) (fun v hv => by rw [evalV_ePl, if_neg hv]) hy

theorem idem_smul_eq (S : HSp D) (R : Pl D → Prop) {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D R) :
    idem D R • y = y :=
  funext fun i => (mem_idAt_iff R (y i)).1 (hy i)

theorem mem_latV_iff_all (S : HSp D) (L : Lat S) (R : Pl D → Prop) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D R) : y ∈ latV S L R ↔ y ∈ latV S L (fun _ => True) := by
  refine ⟨fun h => latV_mono S L (fun _ _ => trivial) h, fun h => ?_⟩
  have h1 := idem_smul_mem S L R h
  rw [idem_smul_eq S R hy] at h1
  exact latV_mono S L (fun _ h => h.2) h1

theorem idem_add_idem (P : Pl D → Prop) {a : AE D} (ha : a ∈ idAt D (fun _ => True)) :
    idem D P * a + idem D (fun p => ¬ P p) * a = a := by
  classical
  rw [← sub_eq_zero]
  apply eq_zero_of_comp
  · rw [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul, infPart_of_idAt ha, mul_zero, mul_zero, add_zero, sub_zero]
  · intro w
    rw [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul, compAt_idem, compAt_idem]
    by_cases h : P w
    · simp [h]
    · simp [h]

theorem mem_latV_iff_parts (S : HSp D) (L : Lat S) (P : Pl D → Prop) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D (fun _ => True)) :
    y ∈ latV S L (fun _ => True) ↔
      idem D (fun p => ¬ P p) • y ∈ latV S L (fun p => ¬ P p) ∧ idem D P • y ∈ latV S L P := by
  constructor
  · intro h
    exact ⟨latV_mono S L (fun _ h => h.2) (idem_smul_mem S L _ h), latV_mono S L (fun _ h => h.2) (idem_smul_mem S L P h)⟩
  · rintro ⟨h1, h2⟩
    have e : y = idem D P • y + idem D (fun p => ¬ P p) • y :=
      funext fun i => (idem_add_idem P (hy i)).symm
    rw [e]
    exact add_mem (latV_mono S L (fun _ _ => trivial) h2) (latV_mono S L (fun _ _ => trivial) h1)

theorem idem_smul_supp (S : HSp D) (R : Pl D → Prop) (y : Fin S.rank → AE D) (i : Fin S.rank) :
    (idem D R • y) i ∈ idAt D R :=
  Ideal.mul_mem_right _ _ (idem_mem_idAt R)

end GlobalTheory.FinPl.MovesSplit


open GlobalTheory.FinPl.MovesSplit GlobalTheory.FinPl.KSplit GlobalTheory.FinPlLoc in
theorem GlobalTheory.FinPl.moves_iff_moves_on_off : ∀ {D : D7} (S : HSp D) (g : GA D S) (L : GlobalTheory.FinPl.Lat S)
    (P : GlobalTheory.FinPl.Pl D → Prop), (GlobalTheory.FinPl.Moves S g L L (fun p => ¬ P p) ∧ GlobalTheory.FinPl.Moves S g L L P) ↔
      GlobalTheory.FinPl.Moves S g L L (fun _ => True) := by
  intro D S g L P
  constructor
  · rintro ⟨hn, hp⟩ y hy
    rw [mem_latV_iff_parts S L P hy, mem_latV_iff_parts S L P (mulVec_mem S _ hy), ← Matrix.mulVec_smul,
      ← Matrix.mulVec_smul]
    exact and_congr (hn _ (idem_smul_supp S _ y)) (hp _ (idem_smul_supp S P y))
  · intro h
    have key : ∀ R : GlobalTheory.FinPl.Pl D → Prop, GlobalTheory.FinPl.Moves S g L L R := by
      intro R y hy
      rw [mem_latV_iff_all S L R hy, mem_latV_iff_all S L R (mulVec_mem S _ hy)]
      exact h y fun i => idAt_mono (fun _ _ => trivial) (hy i)
    exact ⟨key _, key _⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjByColumnUnipotentPreservesUnipotentHaar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR.CjVol

open GlobalTheory.RootEx.VolN GlobalTheory.RootEx.Model

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem colE_inv_val_eq_zero (ρ : ℕ) (β : n → k) (t s : n ⊕ Fin c) (h : lev (ρ + 1) t ≠ lev (ρ + 1) s) :
    (colE c (ρ + 1) β)⁻¹.val t s = 0 := by
  rcases t with t | t <;> rcases s with s | s
  · exact absurd rfl h
  · simp only [colE, upU, Units.inv_mk, fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.of_apply]
    rw [if_neg, neg_zero]
    intro hs; apply h; simp [lev, hs]
  · simp [colE, upU]
  · have : t ≠ s := by rintro rfl; exact h rfl
    simp [colE, upU, Matrix.one_apply, this]

theorem colE_uni (ρ : ℕ) (β : n → k) :
    ∀ r s, (Sum.elim (fun _ => 0) (fun _ => 1) : n ⊕ Fin c → ℕ) s ≤ Sum.elim (fun _ => 0) (fun _ => 1) r →
      (colE c (ρ + 1) β).val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := by
  rintro (r | r) (s | s) h
  · simp [colE, upU, Matrix.one_apply]
  · simp at h
  · simp [colE, upU]
  · simp [colE, upU, Matrix.one_apply]

theorem colE_inv_uni (ρ : ℕ) (β : n → k) :
    ∀ r s, (Sum.elim (fun _ => 0) (fun _ => 1) : n ⊕ Fin c → ℕ) s ≤ Sum.elim (fun _ => 0) (fun _ => 1) r →
      (colE c (ρ + 1) β)⁻¹.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := by
  rintro (r | r) (s | s) h
  · simp [colE, upU, Matrix.one_apply]
  · simp at h
  · simp [colE, upU]
  · simp [colE, upU, Matrix.one_apply]

theorem extendAboveDiagonalEntries_mul_blockRespecting (p : ℕ) (h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (hh : ∀ t s, lev p t ≠ lev p s → h t s = 0) (e : Ix n c p → k) :
    ext0 (Up n c p) e * h = ext0 (Up n c p) ((rm (Up n c p) h).mulVec e) := by
  ext r s
  by_cases hrs : lev p r < lev p s
  · rw [matrixExtendByZero_mul (Up n c p) h e ⟨(r, s), hrs⟩]
    simp [ext0, hrs]
  · have : ext0 (Up n c p) ((rm (Up n c p) h).mulVec e) r s = 0 := by
      simp only [ext0, Matrix.of_apply]; rw [dite_eq_right hrs]
    rw [this, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases hts : lev p t = lev p s
    · have : ext0 (Up n c p) e r t = 0 := by
        simp only [ext0, Matrix.of_apply]; rw [dite_eq_right (show ¬ lev p r < lev p t by rw [hts]; exact hrs)]
      rw [this, zero_mul]
    · rw [hh t s hts, mul_zero]

theorem cjE_mkNel (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β : n → k) (e : Ix n c (ρ + 1) → k) :
    cjE ρ h1 h2 β (mkNel (ρ + 1) e) =
      mkNel (ρ + 1) ((lm (Up n c (ρ + 1)) (colE c (ρ + 1) β).val *
        rm (Up n c (ρ + 1)) (colE c (ρ + 1) β)⁻¹.val).mulVec e) := by
  rw [← mkNel_co (ρ + 1) (cjE ρ h1 h2 β (mkNel (ρ + 1) e))]
  congr 1
  funext a
  have hne : a.1.1 ≠ a.1.2 := fun h => by have := a.2; rw [h] at this; exact lt_irrefl _ this
  rw [← Matrix.mulVec_mulVec, ← mul_matrixExtendSelectedEntriesByZero_apply, ← extendAboveDiagonalEntries_mul_blockRespecting (ρ + 1) _ (colE_inv_val_eq_zero ρ β)]
  simp only [co, cjE_coe, Units.val_mul, val_mkNel, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Units.mul_inv, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.mul_assoc]

theorem det_L (ρ : ℕ) (β : n → k) :
    (lm (Up n c (ρ + 1)) (colE c (ρ + 1) β).val * rm (Up n c (ρ + 1)) (colE c (ρ + 1) β)⁻¹.val).det = 1 := by
  rw [det_mul, det_lm, det_rm]
  rw [Finset.prod_eq_one fun s _ => det_block_unitri _ _ (colE_uni ρ β) _,
    Finset.prod_eq_one fun s _ => det_block_unitri _ _ (colE_inv_uni ρ β) _, mul_one]

end GlobalTheory.HaarR.CjVol

open GlobalTheory.HaarR.CjVol GlobalTheory.RootEx.VolN GlobalTheory.RootEx.Model in
theorem GlobalTheory.HaarR.map_volN_cjE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (ν : Measure k), ν.IsAddHaarMeasure → ∀ β : n → k, (volN ν n c (ρ + 1)).map (cjE ρ h1 h2 β) = volN ν n c (ρ + 1) := by
  intro k _ _ _ _ _ _ n _ _ c ρ h1 h2 ν hν β
  exact map_volN_of_affine ν (ρ + 1) (cjE ρ h1 h2 β) _ (det_L ρ β) 0
    (fun e => by rw [add_zero]; exact cjE_mkNel ρ h1 h2 β e)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFlatMapWeilRepresentationJoint
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.FlatCont

theorem flatAt_om_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vU : VolU D ρ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ Φ, IsThetaFunO ψ V W Φ → Continuous fun q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀ => flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) q.2.1 (om q.1 Φ) q.2.2 := by
  intro D ψ V V₀ W W₀ ρ σ dV dW vS vT χV χW om hom vU x hx Φ hΦ
  have hmaj := _root_.GlobalTheory.Unf.flatFun_majorant D ψ V V₀ W W₀ ρ σ dV dW vS vT χV χW om hom vU x hx Φ hΦ
  have hmix := (_root_.GlobalTheory.MixCont.mixed_coords_continuous D ψ V V₀ W W₀ ρ σ dV dW vS vT χV χW om hom Φ hΦ).2
  have hψ : Continuous ψ := hom.std.1.1
  have htr : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))

  have hval : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) :=
    Units.continuous_val.comp continuous_subtype_val
  have hup : Continuous fun T : Mx D ρ ρ => upSum T := by
    unfold upSum
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact continuous_if_const _ (fun _ => (continuous_apply j).comp (continuous_apply i)) fun _ => continuous_const
  have hpsi : Continuous fun u : UX D ρ => psiUni ψ u.1 :=
    hψ.comp (htr.comp (hup.comp hval))
  have hxu : Continuous fun u : UX D ρ => (rat x : Mx D W.rank ρ) ⬝ u.1.1 :=
    continuous_const.matrix_mul hval

  have hcq : ∀ u : UX D ρ, Continuous fun q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀ =>
      flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) q.2.1 (om q.1 Φ) q.2.2 u := by
    intro u
    unfold flatFun
    refine continuous_const.mul ?_
    have hf : Continuous fun q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀ =>
        ((q.1, ((rat x : Mx D W.rank ρ) ⬝ u.1.1, q.2.1, q.2.2)) :
          (GA D V × GA D W) × Mx D W.rank ρ × Mx D V₀.rank σ × WO V₀ W₀) := by fun_prop
    have h2 := hmix.comp hf
    simp only [Function.comp_def] at h2
    exact h2

  have hcu : ∀ q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀, Continuous fun u : UX D ρ =>
      flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) q.2.1 (om q.1 Φ) q.2.2 u := by
    intro q
    unfold flatFun
    refine (continuous_star.comp hpsi).mul ?_
    have hf : Continuous fun u : UX D ρ =>
        ((q.1, ((rat x : Mx D W.rank ρ) ⬝ u.1.1, q.2.1, q.2.2)) :
          (GA D V × GA D W) × Mx D W.rank ρ × Mx D V₀.rank σ × WO V₀ W₀) :=
      continuous_const.prodMk (hxu.prodMk continuous_const)
    have h2 := hmix.comp hf
    simp only [Function.comp_def] at h2
    exact h2
  haveI : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  haveI : ∀ m n : ℕ, SecondCountableTopology (Mx D m n) := fun m n =>
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → AE D))
  haveI : ∀ m n : ℕ, FirstCountableTopology (Mx D m n) := fun m n =>
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  haveI : ∀ S : HSp D, SecondCountableTopology (GA D S) := fun S => (Formalism.IndefR.Eqv.ga_facts D S).2.2.2.1
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  rw [continuous_iff_continuousAt]
  intro q₀
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds q₀.1
  obtain ⟨M, hMi, hM⟩ := hmaj K hK
  have hev : ∀ᶠ q in nhds q₀, q.1 ∈ K := continuous_fst.continuousAt.preimage_mem_nhds hKn
  have key : ContinuousAt (fun q : (GA D V × GA D W) × Mx D V₀.rank σ × WO V₀ W₀ =>
      ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) q.2.1 (om q.1 Φ) q.2.2 u ∂vU.ν) q₀ := by
    refine continuousAt_of_dominated (bound := M) ?_ ?_ hMi ?_
    · exact Filter.Eventually.of_forall fun q => (hcu q).aestronglyMeasurable
    · exact hev.mono fun q hq => Filter.Eventually.of_forall fun u => hM q.1 hq q.2.1 q.2.2 u
    · exact Filter.Eventually.of_forall fun u => (hcq u).continuousAt
  exact key

end GlobalTheory.FlatCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralMatrixIndicatorMemSchwartzBruhStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceIntegralMatrixIndicator_mem_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'], Place.intInd (k := k) Y Y' ∈ SB (Matrix Y Y' k) := by
  first | exact @GlobalTheory.LocMod.Place.intInd_mem_SB | exact GlobalTheory.LocMod.Place.intInd_mem_SB | (intros; apply GlobalTheory.LocMod.Place.intInd_mem_SB <;> assumption)
end

