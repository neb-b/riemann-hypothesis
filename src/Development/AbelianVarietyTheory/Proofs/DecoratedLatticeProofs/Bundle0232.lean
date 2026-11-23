module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroMemCompletedLatticeSource
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ExtZeroLat

variable {D : D7}

theorem mxAt_mul {P : Pl D → Prop} {a b c : ℕ} {x : Mx D a b} (hx : MxAt P x) (y : Mx D b c) : MxAt P (x ⬝ y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem symplO_add_left (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  simp only [symplO, hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_conjHalf {S T : HSp D} {e : AE D} (he : IsSplitIdem D e) {x y : WO S T}
    (hx : IsHalf (cA D e) x) (hy : IsHalf (cA D e) y) : symplO S T x y = 0 := by
  have h0 : cA D e * cA D (cA D e) = 0 := (GlobalTheory.SplitScalar.isSplitIdem_conj he).2.1
  have : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    rw [← hx d a, ← hy c b, map_mul]
    calc incA D (S.gram⁻¹ a b) * (cA D (cA D e) * cA D (y c b)) * incA D (T.gram c d) * (cA D e * x d a)
        = (cA D e * cA D (cA D e)) * (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) := by ring
      _ = 0 := by rw [h0, zero_mul]
  rw [symplO, this, mul_zero, map_zero]

theorem symplO_resS_symm_left {S A L T : HSp D} (o : OrthDec S A L) (a : WO A T) (t : WO S T) :
    symplO S T ((o.resS T).symm (a, 0)) t = symplO A T a (t ⬝ o.jA) := by
  rw [o.symplO_resS, AddEquiv.apply_symm_apply]
  have h0 : symplO L T 0 ((o.resS T) t).2 = 0 := by simp [symplO, hO]
  rw [h0, add_zero]; rfl

theorem smul_isHalf {e : AE D} (he : e * e = e) {m n : ℕ} (u : Mx D m n) : IsHalf e (e • u) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]

theorem finPart_idem_mem {e : AE D} (he : e * e = e) : finPart D e ∈ intAE D :=
  GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])

end GlobalTheory.FinPl.ExtZeroLat


open GlobalTheory.FinPl.ExtZeroLat in
theorem GlobalTheory.FinPl.ExtZero.extZero_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), (∀ u : WO A T, MxAt (· = p.v) u → (u ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v) ↔ ∀ u' ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v), ψ (symplO A T u u') = 1)) → (∀ u : WO S T, MxAt (· = p.v) u → (u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ↔ ∀ u' ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), ψ (symplO S T u u') = 1)) → halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) = o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT)) → ∀ u ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v), (o.resS T).symm (u, 0) ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
  intro D k _ _ _ _ p n _ _ ψ S A L T o ζ β LA LS LT ΛT hA hS hfac u hu
  classical
  set ΛA := latO A T (LA : Set _) (LT : Set _) (· = p.v) with hΛA
  set ΛS := latO S T (LS : Set _) (LT : Set _) (· = p.v) with hΛS
  have he := p.split
  have hce := GlobalTheory.SplitScalar.isSplitIdem_conj he
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hact := (GlobalTheory.FinPl.placeIdem_acts D p.v ε hε).1

  have hsplit : ∀ {m n : ℕ} (x : Mx D m n), MxAt (· = p.v) x → p.e • x + cA D p.e • x = x := by
    intro m n x hx
    rw [← add_smul, hsum]
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (hact _).1 (hx i j)

  have hcol0 : GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT) 0 = 1 := by
    have hz : GlobalTheory.FinPl.ExtZero.zcol β ζ (0 : WO L T) = 0 := by
      simp only [GlobalTheory.FinPl.ExtZero.zcol, Matrix.zero_mulVec, Pi.zero_apply, map_zero]
      exact Matrix.mulVec_zero _
    have h0 : IsHalf p.e (0 : WO L T) := fun i j => by simp
    simp [GlobalTheory.FinPl.ExtZero.colFun, hz, vecInd, h0]

  have hext : ∀ a ∈ ΛA, IsHalf p.e a → (o.resS T).symm (a, 0) ∈ ΛS := by
    intro a ha hah
    have h1 := congrFun hfac ((o.resS T).symm (a, 0))
    rw [OrthDec.boxS, AddEquiv.apply_symm_apply, hcol0, mul_one] at h1
    have h2 : halfInd p.e ΛA a = 1 := by simp [halfInd, ha, hah]
    rw [h2] at h1
    unfold halfInd at h1
    by_contra hn
    rw [if_neg fun h => hn h.1] at h1
    exact zero_ne_one h1

  have hres : ∀ t ∈ ΛS, IsHalf p.e t → t ⬝ o.jA ∈ ΛA := by
    intro t ht hth
    have h1 := congrFun hfac t
    have h2 : halfInd p.e ΛS t = 1 := by simp [halfInd, ht, hth]
    rw [h2, OrthDec.boxS] at h1
    by_contra hn
    have : halfInd p.e ΛA ((o.resS T) t).1 = 0 := by
      unfold halfInd; rw [if_neg fun h => hn h.1]
    rw [this, zero_mul] at h1
    exact one_ne_zero h1
  have huM : MxAt (· = p.v) u := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have heu : p.e • u ∈ ΛA := GlobalTheory.LatticeStable.smul_mem_latO D A T _ _ _ _ (finPart_idem_mem he.1) u hu
  have hι : (o.resS T).symm (p.e • u, 0) ∈ ΛS := hext _ heu (smul_isHalf he.1 u)
  have hιM : MxAt (· = p.v) ((o.resS T).symm (u, 0)) := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
    exact mxAt_mul huM _
  refine (hS _ hιM).2 fun u' hu' => ?_
  have hu'M : MxAt (· = p.v) u' := GlobalTheory.FinPl.LatMem.latO_mxAt hu'
  have heu' : p.e • u' ∈ ΛS := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_idem_mem he.1) u' hu'
  have hceu' : cA D p.e • u' ∈ ΛS := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_idem_mem hce.1) u' hu'
  rw [symplO_resS_symm_left, ← hsplit u' hu'M, Matrix.add_mul, symplO_add_right, AddChar.map_add_eq_mul]
  have part1 : ψ (symplO A T u ((p.e • u') ⬝ o.jA)) = 1 :=
    (hA u huM).1 hu _ (hres _ heu' (smul_isHalf he.1 u'))
  have part2 : ψ (symplO A T u ((cA D p.e • u') ⬝ o.jA)) = 1 := by
    rw [← hsplit u huM, symplO_add_left, AddChar.map_add_eq_mul]
    have hz : symplO A T (cA D p.e • u) ((cA D p.e • u') ⬝ o.jA) = 0 := by
      refine symplO_conjHalf he (smul_isHalf hce.1 u) ?_
      intro i j
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_assoc, (smul_isHalf hce.1 u') i l]
    rw [hz, AddChar.map_zero_eq_one, mul_one, ← symplO_resS_symm_left]
    exact (hS _ (GlobalTheory.FinPl.LatMem.latO_mxAt hι)).1 hι _ hceu'
  rw [part1, part2, one_mul]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroRightMemCoreLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.ContrComb.LatT

variable {D : D7}

theorem latV_entry_mem {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) (i : Fin S.rank) : y i ∈ idAt D P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, -, hβ, c, -, x, -, rfl⟩ := hz
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hβ _
  | zero => exact zero_mem _
  | add z z' _ _ hz hz' => exact add_mem hz hz'
  | neg z _ hz => exact neg_mem hz

theorem jA_latV {V₀ A L : HSp D} (o : OrthDec V₀ A L) {P : Pl D → Prop} {LA : Lat A} {M : Lat V₀}
    (hLA : IsSelfDualC A LA) (hM : IsSelfDualC V₀ M) (hloc : ∀ v, P v → ∃ LL, OrthAt o M LA LL v)
    {y : Fin A.rank → AE D} (hy : y ∈ latV A LA P) : o.jA *ᵥ y ∈ latV V₀ M P := by
  have hG := _root_.GlobalTheory.FinPl.localComponents D P
  have hy' := ((hG.2 A).2.2.2 LA y hLA.1).1 hy
  refine ((hG.2 V₀).2.2.2 M _ hM.1).2 ⟨fun i => ?_, fun v hv e he => ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy'.1 j)
  · obtain ⟨LL, hLL⟩ := hloc v hv
    have hz := hy'.2 v hv e he
    rw [← Matrix.mulVec_smul]
    refine (hLL _).2 ⟨?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, o.pA_jA, Matrix.one_mulVec]; exact hz
    · rw [Matrix.mulVec_mulVec, o.pB_jA, Matrix.zero_mulVec]; exact zero_mem _

theorem smul_latV_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {w : Fin S.rank → AE D} (hw : w ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • w ∈ latA S L P := by
  induction hw using AddSubgroup.closure_induction with
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

theorem jA_latA {V₀ A L : HSp D} (o : OrthDec V₀ A L) {P : Pl D → Prop} {LA : Lat A} {M : Lat V₀}
    (hLA : IsSelfDualC A LA) (hM : IsSelfDualC V₀ M) (hloc : ∀ v, P v → ∃ LL, OrthAt o M LA LL v)
    {z : Fin A.rank → AE D} (hz : z ∈ latA A LA P) : o.jA *ᵥ z ∈ latA V₀ M P := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hg
    have hsplit : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i) : Fin A.rank → AE D) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    exact smul_latV_mem_latA ha
      (jA_latV o hLA hM hloc (AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, x, hx, rfl⟩))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem latO_extR : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (P : Pl D → Prop) (LA : Lat A) (LS : Lat S)
    (M : Lat V₀), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC V₀ M → (∀ v, P v → ∃ LL, OrthAt o M LA LL v) →
    ∀ u ∈ latO S A (LS : Set _) (LA : Set _) P, (o.resT S).symm (u, 0) ∈ latO S V₀ (LS : Set _) (M : Set _) P := by
  intro D V₀ A L S o P LA LS M hLA hLS hM hloc u hu
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
  have hu' := (_root_.GlobalTheory.FinPl.LatMem.mem_latO_iff D S A LS LA hLS hLA P u).1 hu
  refine (_root_.GlobalTheory.FinPl.LatMem.mem_latO_iff D S V₀ LS M hLS hM P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hu'.1 k j)
  · show (o.jA * u) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec]
    exact jA_latA o hLA hM hloc (hu'.2 y hy)

end GlobalTheory.ContrComb.LatT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroSourceTensorColumnProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

variable {D : D7}

theorem isHalf_mul_right {e : AE D} {l m n : ℕ} {u : Mx D l m} (hu : IsHalf e u) (M : Mx D m n) : IsHalf e (u * M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [← mul_assoc, hu]

theorem isHalf_add_of {e : AE D} {m n : ℕ} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u + v) := by
  intro i j
  simp only [Matrix.add_apply, mul_add, hu i j, hv i j]

theorem isHalf_resS_iff {S A L T : HSp D} (o : OrthDec S A L) (e : AE D) (t : WO S T) :
    IsHalf e t ↔ IsHalf e (t * o.jA) ∧ IsHalf e (t * o.jB) := by
  refine ⟨fun h => ⟨isHalf_mul_right h _, isHalf_mul_right h _⟩, fun h => ?_⟩
  have ht : t = (o.resS T).symm (o.resS T t) := ((o.resS T).symm_apply_apply t).symm
  rw [ht, OrthDec.resS_symm_apply, OrthDec.resS_apply]
  exact isHalf_add_of (isHalf_mul_right h.1 _) (isHalf_mul_right h.2 _)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rd_sum_inl {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S A L T : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1))
    (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (t : WO S T) :
    (rd α₀ β t).submatrix id Sum.inl = rd α β (t * o.jA) := by
  have hs' : α₀.b = fromCols (o.jA.map p.pr * α.b) (replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) := hs
  simp only [rd, hs', Matrix.mul_fromCols]
  ext i j
  simp only [submatrix_apply, id, fromCols_apply_inl]
  rw [Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem rd_sum_inr {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S A L T : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1))
    (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (t : WO S T) :
    (fun i => rd α₀ β t i (Sum.inr 0)) = zcol β ζ (t * o.jB) := by
  have h1 : (t * o.jB) *ᵥ (fun j => incA D (ζ j)) = t *ᵥ ratV (vecB o ζ) := by
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext i
    exact (RingHom.map_mulVec (incA D) o.iB ζ i).symm
  have hs' : α₀.b = fromCols (o.jA.map p.pr * α.b) (replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) := hs
  funext i
  simp only [rd, hs', Matrix.mul_fromCols, fromCols_apply_inr, zcol, h1]
  rw [show (fun i => p.pr ((t *ᵥ ratV (vecB o ζ)) i)) = t.map p.pr *ᵥ fun i => p.pr (ratV (vecB o ζ) i) from
    funext fun i => RingHom.map_mulVec p.pr t _ i]
  rw [Matrix.mulVec_mulVec]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, replicateCol]

theorem extFun_tensCol_sum (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S A L T : HSp D)
    (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n) :
    IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ),
      extFun α₀ β (tensCol Ψ a) = o.boxS T (extFun α β Ψ) (GlobalTheory.FinPl.ExtZero.colFun β ζ a) := by
  intro hs Ψ a
  funext t
  simp only [extFun, OrthDec.boxS, colFun]
  have key : IsHalf p.e t ↔ IsHalf p.e (o.resS T t).1 ∧ IsHalf p.e (o.resS T t).2 := isHalf_resS_iff o p.e t
  by_cases h : IsHalf p.e t
  · obtain ⟨hA, hL⟩ := key.1 h
    rw [if_pos h, if_pos hA, if_pos hL, tensCol, rd_sum_inl o ζ α α₀ β hs, rd_sum_inr o ζ α α₀ β hs]
    rfl
  · rw [if_neg h]
    by_cases hA : IsHalf p.e (o.resS T t).1
    · rw [if_neg fun hL => h (key.2 ⟨hA, hL⟩), mul_zero]
    · rw [if_neg hA, zero_mul]

end GlobalTheory.FinPl.ExtZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroTargetTensorRowProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ExtZero

variable {D : D7}

theorem isHalf_mul {e : AE D} {l m n : ℕ} (M : Mx D l m) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (M ⬝ x) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hx]

theorem isHalf_add {e : AE D} {m n : ℕ} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x + y) := by
  intro i j
  simp only [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem isHalf_resT_iff {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} (t : WO T S) :
    IsHalf e t ↔ IsHalf e (o.pA ⬝ t) ∧ IsHalf e (o.pB ⬝ t) := by
  refine ⟨fun h => ⟨isHalf_mul _ h, isHalf_mul _ h⟩, fun h => ?_⟩
  have := (o.resT T).symm_apply_apply t
  rw [← this, OrthDec.resT_symm_apply, OrthDec.resT_apply]
  exact isHalf_add (isHalf_mul _ h.1) (isHalf_mul _ h.2)

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem map_rat_pr {l m : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E) : (rat M).map p.pr = M.map (p.pr.comp (incA D)) := by
  rw [rat, Matrix.map_map]; rfl

theorem sumFrame_b' {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (hζ : IsLineVec L ζ)
    (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (hs : IsSumFrame o ζ α α₀) :
    α₀.b' = fromRows (α.b' * o.pA.map p.pr)
      (replicateRow (Fin 1) ((p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)))⁻¹ •
        ((fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) ᵥ* o.pB.map p.pr))) := by
  set ι : D.host.E →+* k := p.pr.comp (incA D) with hι
  have hinj : Function.Injective ι := ι.injective
  set c := p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) with hc
  have hc0 : c ≠ 0 := by
    intro h
    apply hζ.2
    apply hinj
    rw [map_zero]; exact h
  set M := fromRows (α.b' * o.pA.map p.pr)
      (replicateRow (Fin 1) (c⁻¹ • ((fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) ᵥ* o.pB.map p.pr))) with hM
  have hcol : (fun i => p.pr (ratV (vecB o ζ) i)) = o.iB.map ι *ᵥ fun j => ι (ζ j) := by
    funext i
    simp only [ratV, vecB]
    exact (RingHom.map_mulVec ι o.iB ζ i)
  have hpA : o.pA.map p.pr = o.qA.map ι := map_rat_pr _
  have hpB : o.pB.map p.pr = o.qB.map ι := map_rat_pr _
  have hjA : o.jA.map p.pr = o.iA.map ι := map_rat_pr _
  have key : M * α₀.b = 1 := by
    rw [hs, hM, Matrix.fromRows_mul, Matrix.mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_fromCols_eq_fromBlocks,
      ← Matrix.fromBlocks_one]
    have eA : o.qA.map ι * o.iA.map ι = 1 := by rw [← Matrix.map_mul, o.qA_iA]; simp
    have eAB : o.qA.map ι * o.iB.map ι = 0 := by rw [← Matrix.map_mul, o.qA_iB]; simp
    have eBA : o.qB.map ι * o.iA.map ι = 0 := by rw [← Matrix.map_mul, o.qB_iA]; simp
    have eB : o.qB.map ι * o.iB.map ι = 1 := by rw [← Matrix.map_mul, o.qB_iB]; simp
    have hu : (fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) = fun j => ι ((star ζ ᵥ* L.gram) j) := rfl
    have hdot : (fun j => ι ((star ζ ᵥ* L.gram) j)) ⬝ᵥ (fun j => ι (ζ j)) = c := by
      rw [hc, Matrix.dotProduct_mulVec, ← RingHom.comp_apply, ← hι, RingHom.map_dotProduct]; rfl
    rw [hcol, hpA, hpB, hjA, hu, ← Matrix.smul_vecMul, Matrix.replicateRow_vecMul, Matrix.replicateCol_mulVec]
    congr 1
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qA.map ι), eA, Matrix.one_mul, α.b'b]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qA.map ι), eAB, Matrix.zero_mul, Matrix.mul_zero]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qB.map ι), eBA, Matrix.zero_mul, Matrix.mul_zero]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qB.map ι), eB, Matrix.one_mul, Matrix.replicateRow_mul_replicateCol]
      ext i j
      simp only [Matrix.of_apply, smul_dotProduct, hdot, smul_eq_mul, inv_mul_cancel₀ hc0]
      fin_cases i; fin_cases j; simp
  calc α₀.b' = (M * α₀.b) * α₀.b' := by rw [key, Matrix.one_mul]
    _ = M := by rw [Matrix.mul_assoc, α₀.bb', Matrix.mul_one]

theorem rd_sumFrame {S A L T : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (hζ : IsLineVec L ζ)
    (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (t : WO T S) :
    rd β α₀ t = fromRows (rd β α (o.pA ⬝ t)) (replicateRow (Fin 1) (zrow β ζ (o.pB ⬝ t))) := by
  rw [rd, sumFrame_b' o ζ hζ α α₀ hs, Matrix.fromRows_mul, Matrix.fromRows_mul]
  congr 1
  · rw [rd, Matrix.map_mul, Matrix.mul_assoc α.b']
  · rw [← Matrix.replicateRow_vecMul, ← Matrix.replicateRow_vecMul]
    congr 1
    have hv : (fun i => p.pr (((fun j => incA D ((star ζ ᵥ* L.gram) j)) ᵥ* (o.pB ⬝ t)) i)) =
        (fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) ᵥ* (o.pB ⬝ t).map p.pr := by
      funext i; exact RingHom.map_vecMul p.pr _ _ i
    rw [zrow, hv, Matrix.map_mul]
    simp only [Matrix.smul_vecMul, Matrix.vecMul_vecMul]

theorem extFun_tensRow (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S A L T : HSp D)
    (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (hζ : IsLineVec L ζ) (α : Frame p A n')
    (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (Ψ : Matrix n' n k → ℂ)
    (b : (n → k) → ℂ) :
    extFun β α₀ (tensRow Ψ b) = o.boxT T (extFun β α Ψ) (GlobalTheory.FinPl.ExtZero.rowFun β ζ b) := by
  funext t
  simp only [OrthDec.boxT, extFun, rowFun]
  rw [OrthDec.resT_apply]
  by_cases h : IsHalf p.e t
  · have h' := (isHalf_resT_iff o t).1 h
    rw [if_pos h, if_pos h'.1, if_pos h'.2, rd_sumFrame o ζ hζ α α₀ β hs t]
    rfl
  · rw [if_neg h]
    by_cases hA : IsHalf p.e (o.pA ⬝ t)
    · rw [if_neg fun hB => h ((isHalf_resT_iff o t).2 ⟨hA, hB⟩), mul_zero]
    · rw [if_neg hA, zero_mul]

end Frames

end GlobalTheory.FinPl.ExtZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergBasisDerivEqOfUniformLimits
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaLimDeriv

theorem tendstoUniformly_heisO {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {G : ℕ → WO S T → ℂ} {F : WO S T → ℂ} (h : TendstoUniformly G F Filter.atTop) (x : ℝ → WO S T) (w : WO S T) :
    TendstoUniformly (fun j t => heisO ψ S T (x t) (G j) w) (fun t => heisO ψ S T (x t) F w) Filter.atTop := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with j hj t
  have := hj (w + x t)
  rw [dist_eq_norm] at this ⊢
  simp only [heisO]
  rw [← mul_sub, norm_mul, hψ.1.2.1, one_mul]
  exact this

theorem heisDer_of_tendstoUniformly : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (G : ℕ → WO S T → ℂ) (F F' : WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (G j)) → TendstoUniformly G F Filter.atTop → ∀ a : (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.heisDer ψ θ a (G j)) F' Filter.atTop → GlobalTheory.Size.heisDer ψ θ a F = F' := by
  intro D ψ hψ θ hθ S T G F F' hG hF a hF'
  have hL := GlobalTheory.OrientedHeis.isRealDir_lineAt (S := S) (T := T) hθ a.1
    (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))
  have e : ∀ f, GlobalTheory.Size.heisDer ψ θ a f = GlobalTheory.OrientedHeis.dLine ψ S T
      (lineAt θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) f := fun _ => rfl
  simp only [e] at hF' ⊢
  generalize lineAt θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) = L at hL hF' ⊢
  funext w
  have h1 := tendstoUniformly_heisO hψ hF L w
  have h2 := tendstoUniformly_heisO hψ hF' L w
  have h3 := hasDerivAt_of_tendstoUniformly h2
    (Filter.Eventually.of_forall fun j s => GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL (hG j) w s)
    (fun s => h1.tendsto_at s) 0
  have h4 := h3.deriv
  rw [map_zero, GlobalTheory.OrientedHeis.heisO_zero] at h4
  exact h4

end GlobalTheory.ThetaLimDeriv

end
end

