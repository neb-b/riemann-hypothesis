module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.LatticeAndConstantUnique
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplit
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open GlobalTheory.Grow GlobalTheory.Unf NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitOrbit

variable {D : D7}

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    hermAt S x y = (fun i => cA D (y i)) ⬝ᵥ (gA S *ᵥ x) := by
  simp only [hermAt, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hermAt_mulVec (S : HSp D) {k : ℕ} (a : Mx D S.rank k) (x : Fin S.rank → AE D) (y : Fin k → AE D) :
    hermAt S x (a *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj a ⬝ gA S) *ᵥ x) := by
  have h : (fun i => cA D ((a *ᵥ y) i)) = (fun i => cA D (y i)) ᵥ* adj a := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hermAt_eq, h, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (adj a)]

theorem hermAt_unitary (S : HSp D) (g : GA D S) (x y : Fin S.rank → AE D) :
    hermAt S (mt S g *ᵥ x) (mt S g *ᵥ y) = hermAt S x y := by
  rw [hermAt_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, mt_unitary, hermAt_eq]

theorem hermAt_jB {S A B : HSp D} (o : OrthDec S A B) (y : Fin S.rank → AE D) (l : Fin B.rank → AE D) :
    hermAt S y (o.jB *ᵥ l) = hermAt B (o.pB *ᵥ y) l := by
  rw [hermAt_mulVec, hermAt_eq, Matrix.mulVec_mulVec, o.pB_eq, ← Matrix.mul_assoc (gA B), gA_mul_giA, Matrix.one_mul]

theorem hermAt_jA {S A B : HSp D} (o : OrthDec S A B) (x : Fin A.rank → AE D) (y : Fin S.rank → AE D) :
    hermAt S (o.jA *ᵥ x) y = hermAt A x (o.pA *ᵥ y) := by
  have h : gA S * o.jA = adj o.pA * gA A := by
    rw [o.gA_eq]
    simp only [Matrix.add_mul, Matrix.mul_assoc, o.pA_jA, o.pB_jA, Matrix.mul_one, Matrix.mul_zero, add_zero]
  rw [hermAt_mulVec, hermAt_eq, Matrix.mulVec_mulVec, h]

theorem exists_den {P : Pl D → Prop} {m n : ℕ} (X : Matrix (Fin m) (Fin n) (AE D)) :
    ∃ N : ℕ, 0 < N ∧ ∀ y : Fin n → AE D, (∀ i, y i ∈ intAt D P) → ∀ i, ((N : AE D) • (X *ᵥ y)) i ∈ intAt D P := by
  choose k hk hX using fun p : Fin m × Fin n => GlobalTheory.LatMatch.exists_nat_smul_intAE (finPart D (X p.1 p.2))
  refine ⟨∏ p, k p, Finset.prod_pos fun p _ => hk p, fun y hy i => ⟨?_, ?_⟩⟩
  · exact Ideal.mul_mem_left _ _ (mulVec_mem_idAt X (fun j => (hy j).1) i)
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, map_sum]
    refine sum_mem fun j _ => ?_
    rw [← mul_assoc, map_mul]
    refine GlobalTheory.LatMatch.mul_mem_intAE' D ?_ (hy j).2
    rw [map_mul, map_natCast, ← nsmul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), mul_smul]
    exact nsmul_mem (hX (i, j)) _

def pre {m n : ℕ} (X : Matrix (Fin m) (Fin n) (AE D)) (Λ : AddSubgroup (Fin m → AE D)) : AddSubgroup (Fin n → AE D) :=
  Λ.comap (Matrix.mulVecLin X).toAddMonoidHom

theorem mem_pre {m n : ℕ} {X : Matrix (Fin m) (Fin n) (AE D)} {Λ : AddSubgroup (Fin m → AE D)} {y : Fin n → AE D} :
    y ∈ pre X Λ ↔ X *ᵥ y ∈ Λ := Iff.rfl

theorem pre_den {P : Pl D → Prop} {m n : ℕ} (X : Matrix (Fin m) (Fin n) (AE D)) {Λ : AddSubgroup (Fin m → AE D)}
    (h : ∃ N : ℕ, 0 < N ∧ ∀ y : Fin m → AE D, (∀ i, y i ∈ intAt D P) → (N : AE D) • y ∈ Λ) :
    ∃ N : ℕ, 0 < N ∧ ∀ y : Fin n → AE D, (∀ i, y i ∈ intAt D P) → (N : AE D) • y ∈ pre X Λ := by
  obtain ⟨N, hN, h⟩ := h
  obtain ⟨N', hN', h'⟩ := exists_den (P := P) X
  refine ⟨N * N', Nat.mul_pos hN hN', fun y hy => ?_⟩
  rw [mem_pre, Matrix.mulVec_smul, Nat.cast_mul, mul_smul]
  exact h _ (h' y hy)

theorem isSDAt_pre_unitary {S : HSp D} {v : Pl D} {Λ : AddSubgroup (Fin S.rank → AE D)} (h : IsSDAt S v Λ) (g : GA D S) :
    IsSDAt S v (pre (mt S g) Λ) := by
  have e : ∀ y, mt S g⁻¹ *ᵥ (mt S g *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mulVec]
  have e' : ∀ y, mt S g *ᵥ (mt S g⁻¹ *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mulVec]
  refine ⟨fun y hy => ?_, pre_den _ h.2.1, fun y hy => ?_⟩
  · rw [← e y]; exact mulVec_mem_idAt _ (h.1 _ hy)
  · rw [mem_pre, h.2.2 _ (mulVec_mem_idAt _ hy)]
    constructor
    · intro H x hx
      rw [← hermAt_unitary S g]; exact H _ hx
    · intro H x hx
      rw [← e' x, hermAt_unitary]
      exact H _ (by rw [mem_pre, e']; exact hx)

theorem split_of_le {S A B : HSp D} (o : OrthDec S A B) {v : Pl D} {M : AddSubgroup (Fin S.rank → AE D)}
    {Λ : AddSubgroup (Fin B.rank → AE D)} (hM : IsSDAt S v M) (hΛ : IsSDAt B v Λ) (hle : ∀ l ∈ Λ, o.jB *ᵥ l ∈ M) :
    IsSDAt A v (pre o.jA M) ∧ ∀ y, y ∈ M ↔ o.pA *ᵥ y ∈ pre o.jA M ∧ o.pB *ᵥ y ∈ Λ := by
  have hsum : ∀ y, o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.sum_eq_one, Matrix.one_mulVec]
  have eA : ∀ x, o.pA *ᵥ (o.jA *ᵥ x) = x := fun x => by rw [Matrix.mulVec_mulVec, o.pA_jA, Matrix.one_mulVec]
  have hB : ∀ y ∈ M, o.pB *ᵥ y ∈ Λ := fun y hy => by
    rw [hΛ.2.2 _ (mulVec_mem_idAt _ (hM.1 y hy))]
    intro l hl
    rw [← hermAt_jB]
    exact (hM.2.2 y (hM.1 y hy)).1 hy _ (hle l hl)
  have hA : ∀ y ∈ M, o.pA *ᵥ y ∈ pre o.jA M := fun y hy => by
    rw [mem_pre, eq_sub_of_add_eq (hsum y)]
    exact sub_mem hy (hle _ (hB y hy))
  refine ⟨⟨fun x hx => ?_, pre_den _ hM.2.1, fun x hx => ?_⟩, fun y => ⟨fun hy => ⟨hA y hy, hB y hy⟩, fun hy => ?_⟩⟩
  · rw [← eA x]; exact mulVec_mem_idAt _ (hM.1 _ hx)
  · rw [mem_pre, hM.2.2 _ (mulVec_mem_idAt _ hx)]
    constructor
    · intro H x' hx'
      rw [← eA x', ← hermAt_jA]; exact H _ hx'
    · intro H y hy
      rw [hermAt_jA]; exact H _ (hA y hy)
  · rw [← hsum y]; exact add_mem hy.1 (hle _ hy.2)

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : incA D a • y ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, h0, b, hb, x, hx, rfl⟩ := hy
    obtain rfl : b = 1 := hb
    refine AddSubgroup.subset_closure ⟨α, hα, h0, a, ha, x, hx, funext fun i => ?_⟩
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (_ ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem smul_mem_latV {S : HSp D} {L : Lat S} {P : Pl D → Prop} {b : D.host.E} (hb : b ∈ D.host.AA⁻¹)
    {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) : incA D b • y ∈ latV S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, h0, a, ha, x, hx, rfl⟩ := hy
    have h1 : a * b ∈ D.host.AA * D.host.AA⁻¹ := FractionalIdeal.mul_mem_mul ha hb
    rw [mul_inv_cancel₀ (GlobalTheory.ModelLatticeCheck.AA_ne_zero D)] at h1
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    refine AddSubgroup.subset_closure ⟨α, hα, h0, 1, rfl, c • x, L.smul_mem c hx, funext fun i => ?_⟩
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] b) * (_ ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, Pi.smul_apply, Algebra.smul_def c, hc, ← mul_assoc, mul_comm b]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mem_latV_of_forall {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (h : ∀ a ∈ D.host.AA, incA D a • y ∈ latA S L P) : y ∈ latV S L P := by
  have key : ∀ c ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) * (D.host.AA⁻¹ : FractionalIdeal _ D.host.E)),
      incA D c • y ∈ latV S L P := by
    intro c hc
    refine Submodule.mul_induction_on hc (fun a ha b hb => ?_) fun c c' h1 h2 => ?_
    · rw [mul_comm, map_mul, mul_smul]
      exact smul_mem_latV hb (h a ha)
    · rw [map_add (f := _), add_smul]; exact add_mem h1 h2
  have := key 1 (by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ (GlobalTheory.ModelLatticeCheck.AA_ne_zero D)]
    exact FractionalIdeal.one_mem_one _)
  rwa [map_one, one_smul] at this

theorem exists_eq_smul {L : HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) (l : Fin L.rank → AE D) :
    ∃ a : AE D, l = a • ratV ζ := by
  have hs : ∀ i j : Fin L.rank, i = j := fun i j => Fin.ext (by have := h.1; omega)
  obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h.2
    rw [show ζ = 0 from funext hcon]
    simp
  refine ⟨l i * incA D (ζ i)⁻¹, funext fun j => ?_⟩
  rw [hs j i, Pi.smul_apply, smul_eq_mul, ratV, mul_assoc, ← map_mul, inv_mul_cancel₀ hi, map_one, mul_one]

theorem ratV_vecB {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) :
    ratV (vecB o ζ) = o.jB *ᵥ ratV ζ :=
  funext fun i => RingHom.map_mulVec (incA D) o.iB ζ i

theorem emb_mem_grpAt {S A B : HSp D} (o : OrthDec S A B) {P : Pl D → Prop} {a : GA D A} (ha : a ∈ grpAt A P) :
    o.emb (a, 1) ∈ grpAt S P := by
  have ha' := (mem_congGrp_iff A (idAt D P) a).1 ha
  refine (mem_congGrp_iff S (idAt D P) _).2 fun i j => ?_
  have e : mt S (o.emb (a, 1)) - 1 = o.jA * (mt A a - 1) * o.pA := by
    rw [o.mt_emb, ← o.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, mt_one, Matrix.mul_one, Matrix.mul_one]
    abel
  rw [← Matrix.sub_apply, e, Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (by rw [Matrix.sub_apply]; exact ha' l k)

theorem line_le {S A L : HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) {L₀ : Lat S} {LA : Lat A}
    {LL : Lat L} {v : Pl D} (hO : OrthAt o L₀ LA LL v) (g : Mx D S.rank S.rank)
    (hz : ∀ a : AE D, a • ratV (vecB o ζ) ∈ latA S L₀ (· = v) → g *ᵥ (a • ratV (vecB o ζ)) ∈ latA S L₀ (· = v))
    (l : Fin L.rank → AE D) (hl : l ∈ latV L LL (· = v)) : o.jB *ᵥ l ∈ pre g (latV S L₀ (· = v)) := by
  have h1 : o.jB *ᵥ l ∈ latV S L₀ (· = v) := by
    refine (hO _).2 ?_
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.pA_jB, o.pB_jB, Matrix.zero_mulVec, Matrix.one_mulVec]
    exact ⟨zero_mem _, hl⟩
  obtain ⟨c, rfl⟩ := exists_eq_smul hζ l
  rw [Matrix.mulVec_smul, ← ratV_vecB] at h1 ⊢
  refine mem_pre.2 (mem_latV_of_forall fun a ha => ?_)
  have h2 := smul_mem_latA ha h1
  rw [smul_smul] at h2
  rw [← Matrix.mulVec_smul, smul_smul]
  exact hz _ h2

theorem moves_of_split {S A B : HSp D} (o : OrthDec S A B) {L₀ : Lat S} {LA : Lat A} {LB : Lat B} {v : Pl D}
    (hO : OrthAt o L₀ LA LB v) (γ : GA D S) (a : GA D A) {Λ : AddSubgroup (Fin A.rank → AE D)}
    (hsplit : ∀ y, y ∈ pre (mt S γ⁻¹) (latV S L₀ (· = v)) ↔ o.pA *ᵥ y ∈ Λ ∧ o.pB *ᵥ y ∈ latV B LB (· = v))
    (hmv : ∀ y : Fin A.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ latV A LA (· = v) ↔ mt A a *ᵥ y ∈ Λ)) :
    Moves S ((o.emb (a, 1))⁻¹ * γ) L₀ L₀ (· = v) := by
  intro y hy
  obtain ⟨z, hzdef⟩ : ∃ z, z = mt S ((o.emb (a, 1))⁻¹ * γ) *ᵥ y := ⟨_, rfl⟩
  rw [← hzdef]
  have hzI : ∀ i, z i ∈ idAt D (· = v) := by rw [hzdef]; exact mulVec_mem_idAt _ hy
  have hw : y = mt S γ⁻¹ *ᵥ (mt S (o.emb (a, 1)) *ᵥ z) := by
    rw [hzdef, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mt_mul, ← mt_mul]
    have : γ⁻¹ * o.emb (a, 1) * ((o.emb (a, 1))⁻¹ * γ) = 1 := by group
    rw [this, mt_one, Matrix.one_mulVec]
  have key := hsplit (mt S (o.emb (a, 1)) *ᵥ z)
  rw [mem_pre, ← hw] at key
  rw [key, hO z, Matrix.mulVec_mulVec, o.pA_emb, Matrix.mulVec_mulVec, o.pB_emb, mt_one, Matrix.one_mul,
    ← Matrix.mulVec_mulVec, ← hmv _ (mulVec_mem_idAt _ hzI)]

theorem orbitSplit : ∀ D : D7, GlobalTheory.FinPl.OrbitSplit D := by
  intro D σ B L₀ v hT hL₀ ⟨LA, LL, hLA, hLL, hO⟩ γ hγ hz
  have hM := isSDAt_pre_unitary (_root_.GlobalTheory.IwaPlace.LocSD.isSDAt_latV D B.V₀ L₀ v hL₀) γ⁻¹
  obtain ⟨hA, hsplit⟩ := split_of_le B.o hM (_root_.GlobalTheory.IwaPlace.LocSD.isSDAt_latV D B.L LL v hLL) (line_le B.o B.line hO _ hz)
  obtain ⟨a, ha, hmv⟩ := _root_.GlobalTheory.IwaOrbit.selfDual_orbit D B.A v _ _ hT (_root_.GlobalTheory.IwaPlace.LocSD.isSDAt_latV D B.A LA v hLA) hA
  exact ⟨a, ha, (B.o.emb (a, 1))⁻¹ * γ, ⟨mul_mem (inv_mem (emb_mem_grpAt B.o ha)) hγ,
    moves_of_split B.o hO γ a hsplit hmv⟩, (mul_inv_cancel_left _ _).symm⟩

end GlobalTheory.FinPl.SplitOrbit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryKeepsBaseLatticeOfSplitComponents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

namespace GlobalTheory.SplitStab

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]

theorem mem_latS_iff (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R))
    (hS : ∀ c : 𝓞 E, Formalism.UG.inclE (F := F) R (c : E) ∈ S)
    (m : ℕ) (t : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin m → E))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ j : Fin m, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = m → t ∣ r))
    (y : Fin m → E ⊗[F] R) :
    y ∈ Formalism.UG.latS (F := F) R S Λ ↔ (∀ j, y j ∈ S) ∧
      ∀ j : Fin m, j.1 + 1 = m → ∃ s ∈ S, y j = Formalism.UG.inclE (F := F) R (t : E) * s := by
  constructor
  · intro hy
    unfold Formalism.UG.latS at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      rw [SetLike.mem_coe, hΛ] at hx
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · obtain ⟨r, hr, -⟩ := hx j
        simp only [hr]; exact hS r
      · obtain ⟨r, hr, hd⟩ := hx j
        obtain ⟨c, rfl⟩ := hd hj
        refine ⟨_, hS c, ?_⟩
        simp only [hr]; push_cast; rw [map_mul]
    | zero => exact ⟨fun j => zero_mem _, fun j _ => ⟨0, zero_mem _, by simp⟩⟩
    | add a b _ _ ha hb =>
      refine ⟨fun j => add_mem (ha.1 j) (hb.1 j), fun j hj => ?_⟩
      obtain ⟨s1, hs1, e1⟩ := ha.2 j hj
      obtain ⟨s2, hs2, e2⟩ := hb.2 j hj
      exact ⟨s1 + s2, add_mem hs1 hs2, by simp [Pi.add_apply, e1, e2, mul_add]⟩
    | smul a b _ hb =>
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
        exact mul_mem a.2 (hb.1 j)
      · obtain ⟨s, hs, e⟩ := hb.2 j hj
        refine ⟨(a : E ⊗[F] R) * s, mul_mem a.2 hs, ?_⟩
        simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, e]
        ring
  · rintro ⟨h1, h2⟩
    have key : ∀ (j : Fin m) (r : 𝓞 E), (j.1 + 1 = m → t ∣ r) → ∀ s ∈ S,
        Pi.single j (s * Formalism.UG.inclE (F := F) R (r : E)) ∈ Formalism.UG.latS (F := F) R S Λ := by
      intro j r hr s hs
      have hx : (Pi.single j (r : E) : Fin m → E) ∈ Λ := by
        rw [hΛ]; intro i
        by_cases hij : i = j
        · subst hij; exact ⟨r, by simp, hr⟩
        · exact ⟨0, by simp [hij], fun _ => dvd_zero _⟩
      have : (Pi.single j (s * Formalism.UG.inclE (F := F) R (r : E)) : Fin m → E ⊗[F] R) =
          (⟨s, hs⟩ : S) • (fun i => Formalism.UG.inclE (F := F) R ((Pi.single j (r : E) : Fin m → E) i)) := by
        ext i; by_cases hij : i = j
        · subst hij; simp [Subring.smul_def]
        · simp [hij, Subring.smul_def]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hx, rfl⟩)
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j.1 + 1 = m
    · obtain ⟨s, hs, e⟩ := h2 j hj
      rw [e, mul_comm]; exact key j t (fun _ => dvd_refl _) s hs
    · simpa using key j 1 (fun h => absurd h hj) (y j) (h1 j)

end GlobalTheory.SplitStab

theorem GlobalTheory.SplitStab.stab_of_split_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (φ : E ⊗[F] v.adicCompletion F →+* k),
    (∀ z, z ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring ↔
      φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR σ (v.adicCompletion F) z) ∈ 𝒪[k]) →
    ∀ (m : ℕ) (t : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin m → E)),
    (∀ x, x ∈ Λ ↔ ∀ j : Fin m, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = m → t ∣ r)) →
    ∀ q : Unif k, valuation k (φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E))) = valuation k ((q.1 : 𝒪[k]) : k) →
    valuation k (φ (Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)))) = 1 →
    ∀ M : GL (Fin m) (E ⊗[F] v.adicCompletion F), M ∈ Formalism.UG.UJ (Formalism.UG.sigR σ (v.adicCompletion F)) 1 →
    ∀ h h' : Matrix (Fin m) (Fin m) k, M.val.map φ = h → h * h' = 1 →
    (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], u r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s) ↔
      ((∀ r, (h *ᵥ u) r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], (h *ᵥ u) r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s)) →
    (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔ ∀ r, (h'ᵀ *ᵥ u) r ∈ 𝒪[k]) →
    M ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) Λ) := by
  intro F E _ _ _ _ _ σ v k _ _ _ _ φ hS m t Λ hΛ q hq hq' M hM h h' hh hhh' hA hB
  have hSO : ∀ c : 𝓞 E, Formalism.UG.inclE (F := F) (v.adicCompletion F) (c : E) ∈
      Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring :=
    fun c => Subring.subset_closure (Or.inl ⟨⟨(c : E), c, rfl⟩, rfl⟩)
  have ht : (t : E) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero, map_zero] at hq
    have h1 : ((q.1 : 𝒪[k]) : k) = 0 := (valuation k).zero_iff.mp hq.symm
    exact q.2.ne_zero (by simpa using h1)
  have hint : ∀ x : k, x ∈ 𝒪[k] ↔ valuation k x ≤ 1 := fun x => Valuation.mem_integer_iff (valuation k) x
  set σ' := Formalism.UG.sigR σ (v.adicCompletion F) with hσ'
  set ι := Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F) with hι

  have hchar : ∀ y : Fin m → E ⊗[F] v.adicCompletion F,
      y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) Λ ↔
      (((∀ r, (fun j => φ (y j)) r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], (fun j => φ (y j)) r0 = φ (ι (t : E)) * s) ∧
        ∀ r, (fun j => φ (σ' (y j))) r ∈ 𝒪[k]) := by
    intro y
    rw [GlobalTheory.SplitStab.mem_latS_iff (F := F) (v.adicCompletion F) _ hSO m t Λ hΛ y]
    simp only [hS]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun r => (h1 r).1, fun r0 hr0 => ?_⟩, fun r => (h1 r).2⟩
      obtain ⟨s, hs, e⟩ := h2 r0 hr0
      exact ⟨φ s, hs.1, by rw [e, map_mul]⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨fun r => ⟨h1 r, h3 r⟩, fun r0 hr0 => ?_⟩
      obtain ⟨s, hs, e⟩ := h2 r0 hr0
      have hu : ι (t : E) * ι ((t : E)⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ ht, map_one]
      refine ⟨ι ((t : E)⁻¹) * y r0, ?_, ?_⟩
      · constructor
        · have hu' : φ (ι ((t : E)⁻¹)) * φ (ι (t : E)) = 1 := by rw [← map_mul, mul_comm, hu, map_one]
          rw [map_mul, show φ (y r0) = φ (ι (t : E)) * s from e, ← mul_assoc, hu', one_mul]
          exact hs
        · have hu' : φ (σ' (ι ((t : E)⁻¹))) * φ (σ' (ι (t : E))) = 1 := by
            rw [← map_mul, ← map_mul, mul_comm, hu, map_one, map_one]
          have hv : valuation k (φ (σ' (ι ((t : E)⁻¹)))) = 1 := by
            have := congrArg (valuation k) hu'
            rw [map_mul, hq', mul_one, map_one] at this
            exact this
          rw [map_mul, map_mul]
          exact mul_mem ((hint _).2 hv.le) (h3 r0)
      · rw [← mul_assoc, hu, one_mul]

  have hU : (M.val.map (φ.comp σ'))ᵀ * h = 1 := by
    have h0 : Formalism.UG.cT σ' (M : Matrix (Fin m) (Fin m) _) * 1 * (M : Matrix (Fin m) (Fin m) _) = 1 := hM
    rw [Matrix.mul_one] at h0
    have := congrArg (fun X => X.map φ) h0
    simp only [Formalism.UG.cT] at this
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_one _ (map_zero φ) (map_one φ)] at this
    rw [← hh]
    simpa [Matrix.transpose_map] using this
  have hh'h : h' * h = 1 := mul_eq_one_comm.mp hhh'
  have hσM : M.val.map (φ.comp σ') = h'ᵀ := by
    have : (M.val.map (φ.comp σ'))ᵀ = h' := by
      calc (M.val.map (φ.comp σ'))ᵀ = (M.val.map (φ.comp σ'))ᵀ * (h * h') := by rw [hhh', Matrix.mul_one]
        _ = h' := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [← this, Matrix.transpose_transpose]
  intro y
  rw [hchar y, hchar]
  have e1 : (fun j => φ (((M : Matrix (Fin m) (Fin m) _) *ᵥ y) j)) = h *ᵥ (fun j => φ (y j)) := by
    funext j; rw [RingHom.map_mulVec, hh]; rfl
  have e2 : (fun j => φ (σ' (((M : Matrix (Fin m) (Fin m) _) *ᵥ y) j))) = h'ᵀ *ᵥ (fun j => φ (σ' (y j))) := by
    funext j
    have := RingHom.map_mulVec (φ.comp σ') (M : Matrix (Fin m) (Fin m) _) y j
    rw [← hσM]
    exact this
  rw [e1, e2]
  exact and_congr (hA _) (hB _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionRankZeroExtRestriction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing MeasureTheory GlobalTheory.FinPl.VLast

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.VLast.KernPf

variable {D : D7}

theorem wittDecomposition_rankZero_coreEmbed_proj {S S₀ : HSp D} (e : HypDec S S₀ 0) : e.j0 ⬝ e.p0 = 1 := by
  have h := e.sum_eq_one
  have h1 : e.jX ⬝ e.pX = 0 := by ext i k; simp [Matrix.mul_apply]
  have h2 : e.jY ⬝ e.pY = 0 := by ext i k; simp [Matrix.mul_apply]
  rwa [h1, h2, zero_add, add_zero] at h

def wittCoreRestrictionHom {S S₀ : HSp D} {ρ : ℕ} (e : HypDec S S₀ ρ) (T : HSp D) : WO S T →+ WO S₀ T where
  toFun w := w ⬝ e.j0
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _

theorem wittCoreRestrictionHom_apply {S S₀ : HSp D} {ρ : ℕ} (e : HypDec S S₀ ρ) (T : HSp D) (w : WO S T) : wittCoreRestrictionHom e T w = w ⬝ e.j0 := rfl

theorem wittDecomposition_rankZero_ext_restriction {S S₀ : HSp D} (e : HypDec S S₀ 0) (T : HSp D) (w : WO S T) : e.ext0 T (wittCoreRestrictionHom e T w) = w := by
  rw [HypDec.matrixExtendByZero_apply, wittCoreRestrictionHom_apply, Matrix.mul_assoc, wittDecomposition_rankZero_coreEmbed_proj, Matrix.mul_one]

end GlobalTheory.FinPl.VLast.KernPf

namespace GlobalTheory.FinPl.VLast.KernPf


end GlobalTheory.FinPl.VLast.KernPf
end
end

