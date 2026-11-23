module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesSelfDualOfSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPl.SelfDualCompl

open GlobalTheory.FinPlLoc

variable {D : D7}

theorem cA_tmul (a : AF D.host.F) (e : D.host.E) : cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) _ (a ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem incA_eq (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

def hA (S : HSp D) (y s : Fin S.rank → AE D) : AE D :=
  ∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * y j

theorem intAt_zero (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [map_neg]; exact neg_mem ha.2⟩

theorem hA_zero_left (S : HSp D) (s : Fin S.rank → AE D) : hA S 0 s = 0 := by
  simp [hA]

theorem hA_add_left (S : HSp D) (y y' s : Fin S.rank → AE D) : hA S (y + y') s = hA S y s + hA S y' s := by
  simp [hA, mul_add, Finset.sum_add_distrib]

theorem hA_neg_left (S : HSp D) (y s : Fin S.rank → AE D) : hA S (-y) s = -hA S y s := by
  simp [hA, Finset.sum_neg_distrib]

theorem hA_zero_right (S : HSp D) (y : Fin S.rank → AE D) : hA S y 0 = 0 := by
  simp [hA]

theorem hA_add_right (S : HSp D) (y s s' : Fin S.rank → AE D) : hA S y (s + s') = hA S y s + hA S y s' := by
  simp [hA, add_mul, Finset.sum_add_distrib]

theorem hA_neg_right (S : HSp D) (y s : Fin S.rank → AE D) : hA S y (-s) = -hA S y s := by
  simp [hA, Finset.sum_neg_distrib]

theorem hA_gen (S : HSp D) (α β : Af D.host.F) (x x' : Fin S.rank → D.host.E) :
    hA S (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x j)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
      pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] (∑ i, ∑ j, star (x' i) * HSpace.gram S i j * x j) := by
  simp only [hA, cA_tmul, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← TensorProduct.tmul_sum,
    pairA_mul]

theorem hA_mem {S : HSp D} {LS : Lat S} (hS : IsSelfDualC S LS) {P : Pl D → Prop} {y s : Fin S.rank → AE D}
    (hy : y ∈ latV S LS P) (hs : s ∈ latV S LS P) : hA S y s ∈ intAt D P := by
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨β, hβi, hβ, a, ha, x', hx', rfl⟩ := hs
    rw [Set.mem_singleton_iff] at ha
    subst ha
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      rw [hA_gen]
      obtain ⟨c, hc⟩ := (hS.2 x).1 hx x' hx'
      rw [← hc]
      refine ⟨pair_mem_idAt P _ (fun v hv => by rw [map_mul, hα v hv, mul_zero]) _, ?_⟩
      rw [finPart_pair]
      exact AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβi hαi, c, rfl⟩
    | zero => rw [hA_zero_left]; exact intAt_zero P
    | add y y' _ _ h h' => rw [hA_add_left]; exact intAt_add h h'
    | neg y _ h => rw [hA_neg_left]; exact intAt_neg h
  | zero => rw [hA_zero_right]; exact intAt_zero P
  | add s s' _ _ h h' => rw [hA_add_right]; exact intAt_add h h'
  | neg s _ h => rw [hA_neg_right]; exact intAt_neg h

theorem wachExpansion_smul_compatible {S : HSp D} {LS : Lat S} (P : Pl D → Prop) {s : Fin S.rank → D.host.E} (hs : s ∈ LS)
    {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    (idem D P * finIn D z) • (fun l => incA D (s l)) ∈ latV S LS P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, o, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨ePl D P * a, GlobalTheory.FinPl.LatMem.intAf_mul' (ePl_int P) ha,
      fun w hw => by rw [map_mul, evalV_ePl, if_neg hw, zero_mul], 1, rfl, o • s, LS.smul_mem o hs, ?_⟩
    funext l
    simp only [Pi.smul_apply, smul_eq_mul, idem, finIn_tmul, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, pairA_mul,
      mul_one, one_mul]
    congr 1
  | zero => rw [map_zero, mul_zero, zero_smul]; exact zero_mem _
  | add z z' _ _ h h' => rw [map_add (f := _), mul_add, add_smul]; exact add_mem h h'
  | neg z _ h => rw [map_neg, mul_neg, neg_smul]; exact neg_mem h

theorem smul_mem {S : HSp D} {LS : Lat S} {P : Pl D → Prop} {c : AE D} (hc : c ∈ intAt D P) {s : Fin S.rank → D.host.E}
    (hs : s ∈ LS) : c • (fun l => incA D (s l)) ∈ latV S LS P := by
  have h1 : idem D P * c = c := (mem_idAt_iff P c).1 hc.1
  have h2 : c = finIn D (finPart D c) := eq_finIn (infPart_of_idAt hc.1)
  have := wachExpansion_smul_compatible P hs hc.2
  rwa [← h2, h1] at this

theorem cA_test (P : Pl D → Prop) (e : D.host.E) :
    cA D (pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 * e)) = idem D P * incA D (star e) := by
  rw [cA_tmul, idem, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, mul_one]

theorem selfDual_latV : ∀ (D : D7) (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ (P : Pl D → Prop)
    (y : Fin S.rank → AE D), (∀ r, y r ∈ idAt D P) →
    (y ∈ latV S LS P ↔ ∀ s ∈ latV S LS P, (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * y j) ∈ intAt D P) := by
  intro D S LS hS P y hy
  refine ⟨fun h s hs => hA_mem hS h hs, fun h => ?_⟩
  obtain ⟨m, s, s', hs, hs', hdual⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hS
  let t : Fin m → Fin S.rank → AE D := fun i l => pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 * s' i l)
  have ht : ∀ i, t i ∈ latV S LS P := fun i =>
    AddSubgroup.subset_closure ⟨ePl D P, ePl_int P, fun w hw => by rw [evalV_ePl, if_neg hw], 1, rfl, s' i, hs' i, rfl⟩
  have hyeq : y = ∑ i, hA S y (t i) • (fun a => incA D (s i a)) := by
    funext a
    have hya : y a = idem D P * y a := ((mem_idAt_iff P (y a)).1 (hy a)).symm
    have hsum : ∀ j, idem D P * y j * incA D (if a = j then 1 else 0) = if a = j then idem D P * y j else 0 := by
      intro j
      split_ifs <;> simp
    calc y a = ∑ j, idem D P * y j * incA D (if a = j then 1 else 0) := by
          rw [Finset.sum_congr rfl fun j _ => hsum j, Finset.sum_ite_eq, if_pos (Finset.mem_univ a)]
          exact hya
      _ = ∑ j, idem D P * y j * incA D (∑ i, s i a * ∑ k, star (s' i k) * HSpace.gram S k j) := by
          simp only [hdual]
      _ = _ := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hA, t, cA_test, map_sum, map_mul, Finset.mul_sum,
            Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
          ring
  rw [hyeq]
  exact sum_mem fun i _ => smul_mem (h (t i) (ht i)) (hs i)

end GlobalTheory.FinPl.SelfDualCompl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineProjectionMemHomLatticeCompletion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LineProj

open GlobalTheory.IwaPlace

variable {D : D7}

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    hermAt S x y = (fun i => cA D (y i)) ⬝ᵥ (gA S *ᵥ x) := by
  simp only [hermAt, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hermAt_mulVec (S : HSp D) {π : Mx D S.rank S.rank} (h : adj π ⬝ gA S = gA S ⬝ π) (x y : Fin S.rank → AE D) :
    hermAt S (π *ᵥ x) y = hermAt S x (π *ᵥ y) := by
  have e : (fun i => cA D ((π *ᵥ y) i)) = (fun i => cA D (y i)) ᵥ* adj π := by
    funext i
    rw [adj, Matrix.vecMul_transpose]
    exact RingHom.map_mulVec (cA D) π y i
  have e2 : gA S *ᵥ (π *ᵥ x) = adj π *ᵥ (gA S *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x) h.symm
  rw [hermAt_eq, hermAt_eq, e, e2]
  exact Matrix.dotProduct_mulVec _ _ _

theorem hermAt_smul (S : HSp D) (a : AE D) (x y : Fin S.rank → AE D) :
    hermAt S (a • x) y = hermAt S x (cA D a • y) := by
  simp only [hermAt, Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.DualPairCheck.cA_cA]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermAt_add_left (S : HSp D) (x x' y : Fin S.rank → AE D) :
    hermAt S (x + x') y = hermAt S x y + hermAt S x' y := by
  simp only [hermAt, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem add_mem_intAt {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩

theorem proj_selfAdj {S A L : HSp D} (o : OrthDec S A L) :
    adj (o.jB ⬝ o.pB) ⬝ gA S = gA S ⬝ (o.jB ⬝ o.pB) := by
  rw [o.pB_eq]
  simp only [adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_mem_of_half (p : SplitPt D k) {S : HSp D} {M : Lat S} (hM : IsSelfDualC S M) {π : Mx D S.rank S.rank}
    (h : adj π ⬝ gA S = gA S ⬝ π)
    (hw : ∀ z ∈ latV S M (· = p.v), π *ᵥ (p.e • z) ∈ latV S M (· = p.v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S M (· = p.v)) : π *ᵥ y ∈ latV S M (· = p.v) := by
  obtain ⟨hs, -, hd⟩ := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S M p.v hM
  refine (hd _ (mulVec_mem_idAt π (hs y hy))).2 fun x hx => ?_
  have hy' : y = p.e • y + cA D p.e • y := by
    funext i
    rw [← add_smul, Pi.smul_apply, smul_eq_mul]
    exact ((FrameLat.idem_iff p (y i)).1 (hs y hy i)).symm
  rw [hy', Matrix.mulVec_add, hermAt_add_left]
  refine add_mem_intAt ((hd _ (hs _ (hw y hy))).1 (hw y hy) x hx) ?_
  rw [hermAt_mulVec S h, hermAt_smul, GlobalTheory.DualPairCheck.cA_cA, ← Matrix.mulVec_smul]
  exact (hd y (hs y hy)).1 hy _ (hw x hx)

theorem proj_frame {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {S A L : HSp D} (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) {α : Frame p A n} {α₀ : Frame p S (n ⊕ Fin 1)} (h : IsSumFrame o ζ α α₀)
    (x : n ⊕ Fin 1 → k) :
    (o.jB ⬝ o.pB).map p.pr *ᵥ (α₀.b *ᵥ x) = α₀.b *ᵥ Sum.elim 0 (x ∘ Sum.inr) := by
  have h1 : (o.jB * o.pB).map p.pr * o.jA.map p.pr = 0 := by
    rw [← Matrix.map_mul, Matrix.mul_assoc, o.pB_jA, Matrix.mul_zero]
    exact Matrix.map_zero _ (map_zero _)
  have h2 : (o.jB * o.pB) *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
    have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
      funext i
      exact RingHom.map_mulVec (incA D) o.iB ζ i
    rw [e, Matrix.mulVec_mulVec, Matrix.mul_assoc, o.pB_jB, Matrix.mul_one]
  have h3 : (o.jB * o.pB).map p.pr *ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) = fun i => p.pr (ratV (vecB o ζ) i) := by
    funext i
    have := RingHom.map_mulVec p.pr (o.jB * o.pB) (ratV (vecB o ζ)) i
    rw [h2] at this
    exact this.symm
  rw [IsSumFrame] at h
  rw [h, Matrix.mulVec_mulVec, Matrix.mul_fromCols, ← Matrix.mul_assoc, h1, Matrix.zero_mul,
    ← Matrix.replicateCol_mulVec, h3, Matrix.fromCols_mulVec, Matrix.fromCols_mulVec_sumElim, Matrix.zero_mulVec,
    Matrix.mulVec_zero]

theorem proj_half {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {S A L : HSp D} (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) {α : Frame p A n} {α₀ : Frame p S (n ⊕ Fin 1)} (h : IsSumFrame o ζ α α₀)
    {M : Lat S} {Λ : Submodule 𝒪[k] (n → k)} (hΛ : α₀.IsLat M (lastKer Λ)) {z : Fin S.rank → AE D}
    (hz : z ∈ latV S M (· = p.v)) : (o.jB ⬝ o.pB) *ᵥ (p.e • z) ∈ latV S M (· = p.v) := by
  have hb : α₀.b *ᵥ (α₀.b' *ᵥ fun i => p.pr (z i)) = fun i => p.pr (z i) := by
    rw [Matrix.mulVec_mulVec, α₀.bb', Matrix.one_mulVec]
  have h1 : (α₀.b' *ᵥ fun i => p.pr (z i)) ∈ lastKer Λ := by
    refine (hΛ _).2 ?_
    rw [hb]
    simp only [p.sec_pr]
    exact GlobalTheory.FinPlLoc.smul_latV p.v (FrameLat.e_mem_intAt p) hz
  have h2 : (Sum.elim 0 ((α₀.b' *ᵥ fun i => p.pr (z i)) ∘ Sum.inr) : n ⊕ Fin 1 → k) ∈ lastKer Λ :=
    GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨Λ.zero_mem, (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 h1).2⟩
  have h3 := (hΛ _).1 h2
  rw [← proj_frame o ζ h, hb] at h3
  convert h3 using 1
  funext i
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← p.sec_pr, RingHom.map_mulVec]
  rfl

theorem lineProj_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (Λ : ι → Submodule 𝒪[k] (n' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ x ∈ latO B.V₀ S (M : Set _) (LS : Set _) P, (B.o.resS S).symm (0, (B.o.resS S x).2) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P := by
  intro D k _ _ _ _ ι p I P hP n' _ _ ρ B S α α₀ M LS Λ hM hLS h x hx
  have hπ : ∀ y ∈ latV B.V₀ M P, (B.o.jB * B.o.pB) *ᵥ y ∈ latV B.V₀ M P := by
    intro y hy
    refine (GlobalTheory.FinPlLoc.part_lat P B.V₀ M _ hM.1).2 ⟨mulVec_mem_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy), fun v hv e he => ?_⟩
    obtain ⟨i, rfl⟩ := (hP.mem v).1 hv
    rw [← Matrix.mulVec_smul]
    exact mulVec_mem_of_half (p i) hM (proj_selfAdj B.o) (fun z hz => proj_half B.o B.ζ (h i).1 (h i).2 hz)
      (GlobalTheory.FinPlLoc.smul_latV _ he hy)
  obtain ⟨hx1, hx2⟩ := (GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ S M LS hM hLS P x).1 hx
  have e : (B.o.resS S).symm (0, (B.o.resS S x).2) = x * (B.o.jB * B.o.pB) := by
    rw [OrthDec.resS_symm_apply, OrthDec.resS_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc]
  rw [e]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ S M LS hM hLS P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx1 i l)
  · have := hx2 _ (hπ y hy)
    rwa [Matrix.mulVec_mulVec] at this

end GlobalTheory.LineProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLocalLatticeIffOfFiniteAdelicCompletionMap
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.LocFromGlob

open scoped TensorProduct

theorem mem_latLoc_iff_of_latHat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L L' : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (hL' : L'.FG) (b : GL (Fin n) (TensorProduct F (Af F) E))
    (hb : ∀ w, w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔
      b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L' : Set (Fin n → E)))
    (v : HeightOneSpectrum (𝓞 F)) (z : Fin n → TensorProduct F (Fv F v) E) :
    z ∈ latLoc F L v ↔
      (Formalism.UG.bc (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom b).val *ᵥ z ∈ latLoc F L' v := by

  let ext : (Fin n → Fv F v ⊗[F] E) → (Fin n → Af F ⊗[F] E) :=
    fun z i => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v) (z i)
  have hself : ∀ z, GlobalTheory.AdelicU.vecLoc v (ext z) = z := fun z =>
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_self _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_self v) _
  have hne : ∀ z u, u ≠ v → GlobalTheory.AdelicU.vecLoc u (ext z) = 0 := fun z u hu =>
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_ne hu) _
  have hmul : ∀ (g : GL (Fin n) (TensorProduct F (Af F) E)) u y, GlobalTheory.AdelicU.vecLoc u (g.val *ᵥ y) =
      (Formalism.UG.bc (Algebra.TensorProduct.map (evalV F u) (AlgHom.id F E)).toRingHom g).val *ᵥ
        GlobalTheory.AdelicU.vecLoc u y := fun g u y => funext fun i =>
    RingHom.map_mulVec (Algebra.TensorProduct.map (evalV F u) (AlgHom.id F E)).toRingHom _ y i
  have hext : ∀ (M : Submodule (𝓞 E) (Fin n → E)), M.FG → ∀ z, z ∈ latLoc F M v →
      ext z ∈ Formalism.MainNotions.StandardLattice.latHat F E (M : Set (Fin n → E)) := fun M hM z hz => by
    rw [GlobalTheory.AdelicU.mem_latHat_iff hM]
    intro u
    by_cases e : u = v
    · subst e; rw [hself]; exact hz
    · rw [hne z u e]; exact zero_mem _
  constructor
  · intro hz
    have h1 := (GlobalTheory.AdelicU.mem_latHat_iff hL' _).1 ((hb _).1 (hext L hL z hz)) v
    rwa [hmul, hself] at h1
  · intro hz
    have h1 := hext L' hL' _ hz
    set y := ext ((Formalism.UG.bc (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom b).val *ᵥ z)
    have h2 : b.val *ᵥ ((b⁻¹).val *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have h3 := (GlobalTheory.AdelicU.mem_latHat_iff hL _).1 ((hb _).2 (h2 ▸ h1)) v
    rw [hmul, hself, Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec] at h3
    exact h3

end GlobalTheory.Core.LocFromGlob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawScalarFormsContinuousAutomorphicCentral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem RealD.r_center_scalar {c : Comm D} (ρ : RealD c) (hρ : ρ.Is) (j : ℕ) (hj : j ≤ D.R.m) {z : GA D (c.X j)}
    (hz : z ∈ GinfC (c.X j)) (hzc : z ∈ Subgroup.center (GA D (c.X j))) (τ : D.what₂.Tau) :
    ρ.r j hj z τ = (Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) • (1 : Matrix (Fin (ρ.N j)) (Fin (ρ.N j)) ℂ) := by
  have hu := hρ.uni j hj
  obtain ⟨ζ, hζ⟩ := GlobalTheory.CenterScalar.scalar_of_comm_unitary (ρ.r j hj z τ) fun U hU => by
    obtain ⟨k, hk⟩ := hu.onto (fun _ => U) fun _ => (Matrix.mem_unitaryGroup_iff').2 hU
    have e1 := hu.mul k ⟨z, hz⟩ τ
    have e2 := hu.mul ⟨z, hz⟩ k τ
    have hkz : (k * ⟨z, hz⟩ : GinfC (c.X j)) = ⟨z, hz⟩ * k :=
      Subtype.ext ((Subgroup.mem_center_iff.1 hzc) k.1)
    rw [hkz, e2] at e1
    have hk' : ρ.r j hj k.1 τ = U := congrFun hk τ
    rw [hk'] at e1
    exact e1.symm
  rcases Nat.eq_zero_or_pos (ρ.N j) with h0 | hpos
  · ext a
    exact absurd a.2 (by omega)
  · rw [hζ, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
      mul_div_assoc, div_self (by exact_mod_cast hpos.ne'), mul_one]

theorem rdX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → RdX t := by
  intro D c 𝒯 t hc _ hP j hj
  obtain ⟨ρ, hρ, H⟩ := hP
  refine ⟨fun z => ∏ τ, (Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) ^ (∑ i, (ρ.lam j τ).w i), fun s ψ hψ α y => ?_⟩
  obtain ⟨⟨A, hA⟩, -⟩ := H s
  obtain ⟨h1, -, h3, h4⟩ := _root_.GlobalTheory.SeeSaw.scalarForm_laws D c (t s) ρ A hc hρ hA.1 j hj ψ hψ α
  refine ⟨h1 y, fun z hz hzc g => ?_⟩
  have hdet : ∀ τ, IsUnit (ρ.r j hj z τ).det := fun τ =>
    Matrix.isUnit_det_of_left_inverse ((Matrix.mem_unitaryGroup_iff').1 ((hρ.uni j hj).uni ⟨z, hz⟩ τ))
  set w := (ρ.fr j y).tr (ρ.r j hj z) hdet with hw
  have e1 : (t s).rd j α ψ y (g * z) = (t s).rd j α ψ ((ρ.fr j).symm w) g :=
    h3 y _ g z hz (by rw [Equiv.apply_symm_apply]; exact Frames.isTr_tr _ hdet _)
  have e2 := (GlobalTheory.KJInf.valC_poly _ _ _ _ |>.2.2.2) _ (h4 g) (fun τ => Matrix.trace (ρ.r j hj z τ) / (ρ.N j : ℂ)) (ρ.fr j y) w
    (fun τ => by
      show ρ.r j hj z τ * (ρ.fr j y).1 τ = _
      conv_lhs => rw [ρ.r_center_scalar hρ j hj hz hzc τ]
      rw [Matrix.smul_mul, Matrix.one_mul])
  simp only [Equiv.symm_apply_apply] at e2
  rw [e1, e2]

end GlobalTheory.SeeSaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelLeviDeterminantIntegralSelfDualLattice
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Core.Rk.AInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_mem_intLoc_of_mapsTo {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L]
    (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hX : ∀ x ∈ latLoc F L v, X *ᵥ x ∈ latLoc F L v) : X.det ∈ intLoc F E v := by
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  set b := Formalism.UG.bc (compFin F E v) a with hb
  set N : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (b⁻¹).1 * X * b.1 with hN
  have hent : ∀ i j, N i j ∈ intLoc F E v := by
    intro i j
    have h1 : b.1 *ᵥ (Pi.single j 1 : Fin n → Fv F v ⊗[F] E) ∈ latLoc F L v :=
      (ha v (Pi.single j 1)).1 fun l => by
        by_cases e : l = j
        · subst e; simp
        · simp [e]
    have h2 := hX _ h1
    have hbN : b.1 * N = X * b.1 := by
      rw [hN, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    have h3 : b.1 *ᵥ (N *ᵥ Pi.single j 1) ∈ latLoc F L v := by
      rwa [Matrix.mulVec_mulVec, hbN, ← Matrix.mulVec_mulVec]
    have h4 := (ha v _).2 h3 i
    simpa using h4
  have hdet : N.det = X.det := by
    rw [hN, Matrix.det_mul, Matrix.det_mul, mul_comm ((b⁻¹).1.det * X.det), ← mul_assoc, ← Matrix.det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]
  let N' : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i j => ⟨N i j, hent i j⟩
  have hmap : N'.map (intLoc F E v).subtype = N := by ext i j; rfl
  have hd := RingHom.map_det (intLoc F E v).subtype N'
  rw [← hdet, ← hmap, ← RingHom.mapMatrix_apply, ← hd]
  exact (N'.det).2

theorem aH_mem_intLoc_of_lattice (σ : E →ₐ[F] E) {n : ℕ} (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F))
    (p : siegelH (Fv F v) σ Q) (hp : (p : GLoc σ Q v) ∈ GlobalTheory.Doubling.KFin σ Q L v) :
    ((aH _ σ Q p : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v := by
  have hk : KeepsDiag finSumFinEquiv (GlobalTheory.AdelicU.matHom (Fv F v) σ Q p).1 :=
    (mem_siegelOf (e := finSumFinEquiv) (mat := GlobalTheory.AdelicU.matHom (Fv F v) σ Q)).1 p.2
  refine det_mem_intLoc_of_mapsTo L v (leviMat finSumFinEquiv (GlobalTheory.AdelicU.matHom (Fv F v) σ Q p).1) fun x hx => ?_
  have h1 : pairVec finSumFinEquiv x x ∈ latLoc F (sumLat finSumFinEquiv L L) v := by
    rw [latLoc_sumLat]; exact (pairVec_mem_sumLat _).2 ⟨hx, hx⟩
  have h2 := (mem_stabLoc.1 hp _).1 h1
  rw [hk.mulVec_diag, latLoc_sumLat, pairVec_mem_sumLat] at h2
  exact h2.1

theorem aH_mem_intLoc : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (v : FinPl D) (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram), (p : Gv (dblSp A) v) ∈ KFin D.sp.cm.sig (dblSp A).gram L v → ((aH _ D.sp.cm.sig (dblSp A).gram p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v := by
  intro D A L hL v p hp
  haveI := GlobalTheory.AdIsom.selfDual_isFullLattice hL
  exact aH_mem_intLoc_of_lattice D.sp.cm.sig (n := A.rank) (dblSp A).gram L v p hp

end GlobalTheory.Core.Rk.AInt
end
end

