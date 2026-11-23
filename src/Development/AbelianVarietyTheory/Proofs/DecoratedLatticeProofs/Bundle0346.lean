module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawProdLocalCellsDistinctPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.CellProd

theorem prod_ofFn_mul {M : Type} [Monoid M] : ∀ {n : ℕ} (r u : Fin n → M), (∀ i i', i ≠ i' → Commute (u i) (r i')) →
    (List.ofFn fun i => r i * u i).prod = (List.ofFn r).prod * (List.ofFn u).prod
  | 0, _, _, _ => by simp
  | n + 1, r, u, h => by
    have ih := prod_ofFn_mul (fun i => r i.succ) (fun i => u i.succ)
      (fun i i' hi => h _ _ fun e => hi (Fin.succ_injective _ e))
    have hc : Commute (u 0) (List.ofFn fun i : Fin n => r i.succ).prod := by
      refine Commute.list_prod_right _ _ ?_
      rw [List.forall_mem_ofFn_iff]
      intro i
      exact h _ _ (Fin.succ_ne_zero i).symm
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih, mul_assoc, mul_assoc, ← mul_assoc (u 0), hc.eq, mul_assoc]

theorem prod_ofFn_single {M : Type} [Monoid M] : ∀ {n : ℕ} (f : Fin n → M) (i : Fin n), (∀ i', i' ≠ i → f i' = 1) →
    (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | n + 1, f, i, h => by
    simp only [List.ofFn_succ, List.prod_cons]
    induction i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      rw [List.forall_mem_ofFn_iff]
      intro i
      exact h _ (Fin.succ_ne_zero i)
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact prod_ofFn_single (fun i => f i.succ) i fun i' hi => h _ fun e => hi (Fin.succ_injective _ e)

variable {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem idAt_le {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : idAt D P ≤ idAt D P' :=
  inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hw => w.2 (h _ hw)⟩ le_rfl)

theorem mem_idAt (q : SplitPt D k) {a : AE D} (h : (q.e + cA D q.e) * a = a) : a ∈ idAt D (· = q.v) := by
  obtain ⟨ε, hε, hs⟩ := q.above
  exact ((placeIdem_acts D q.v ε hε).1 a).2 (hs ▸ h)

theorem idem_mul_eq_zero (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {a : AE D}
    (h : (q'.e + cA D q'.e) * a = a) : (q.e + cA D q.e) * a = 0 := by
  obtain ⟨ε, hε, hs⟩ := q.above
  rw [hs]
  exact (placeIdem_acts D q.v ε hε).2 a (idAt_le (fun v (e : v = q'.v) => e ▸ hv) (mem_idAt q' h))

theorem pr_eq_zero (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {a : AE D}
    (h : (q'.e + cA D q'.e) * a = a) : q.pr a = 0 := by
  have h0 := idem_mul_eq_zero q q' hv h
  obtain ⟨h1, h2, -⟩ := q.split
  have : q.e * a = 0 := by
    have := congrArg (q.e * ·) h0
    simpa only [← mul_assoc, mul_add, h1, h2, add_zero, mul_zero] using this
  rw [← q.pr_sec (q.pr a), q.sec_pr, this, map_zero]

theorem mem_grpAt (q : SplitPt D k) {V : HSp D} {g : GA D V} (hg : SuppAt q.e V g) {P : Pl D → Prop} (hP : P q.v) :
    g ∈ grpAt V P := by
  rw [grpAt, congGrp, MonoidHom.mem_ker]
  ext i j
  change Ideal.Quotient.mk _ (mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
  rw [← Matrix.map_one (Ideal.Quotient.mk (idAt D P)) (map_zero _) (map_one _), Matrix.map_apply, Ideal.Quotient.eq]
  exact idAt_le (fun v (e : v = q.v) => e ▸ hP) (mem_idAt q (hg i j))

theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  simp [Formalism.L2.Theta.mt]

theorem sub_mul_sub (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {V : HSp D} {g h : GA D V}
    (hg : SuppAt q.e V g) (hh : SuppAt q'.e V h) :
    (mt V g - 1) * (mt V h - 1) = 0 ∧ (mt V h - 1) * (mt V g - 1) = 0 := by
  have key : ∀ a b c d, (mt V g - 1) a b * (mt V h - 1) c d = 0 := fun a b c d => by
    rw [← hg a b, mul_comm (q.e + _), mul_assoc, idem_mul_eq_zero q q' hv (hh c d), mul_zero]
  constructor
  · ext a b
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => key _ _ _ _
  · ext a b
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => by rw [mul_comm]; exact key _ _ _ _

theorem commute_of_suppAt (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {V : HSp D} {g h : GA D V}
    (hg : SuppAt q.e V g) (hh : SuppAt q'.e V h) : Commute g h := by
  obtain ⟨h1, h2⟩ := sub_mul_sub q q' hv hg hh
  have : mt V (g * h) = mt V (h * g) := by
    rw [mt_mul', mt_mul', ← sub_eq_zero]
    have e : mt V g * mt V h - mt V h * mt V g = (mt V g - 1) * (mt V h - 1) - (mt V h - 1) * (mt V g - 1) := by
      noncomm_ring
    rw [e, h1, h2, sub_zero]
  exact Subtype.ext (Units.ext this)

theorem map_eq_one (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {V : HSp D} {g : GA D V}
    (hg : SuppAt q'.e V g) : (mt V g).map q.pr = 1 := by
  ext i j
  have := pr_eq_zero q q' hv (hg i j)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, ← Matrix.map_one q.pr (map_zero _) (map_one _), Matrix.map_apply]

def matAt (q : SplitPt D k) (V : HSp D) : GA D V →* Matrix (Fin V.rank) (Fin V.rank) k :=
  (q.pr.mapMatrix.toMonoidHom.comp (Units.coeHom _)).comp (matHom V)

end GlobalTheory.SeeSaw.CellProd


open GlobalTheory.SeeSaw.CellProd in
theorem GlobalTheory.SeeSaw.prod_local_cells : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ), j' < D.R.m → ∀ (R : Subgroup (GA D (c.V j'))) (b : Fin n → ℕ) (hb : ∀ i, j' + b i = (G i).s + 1) (xs : Fin n → GA D (c.V j')), (∀ i, ∃ r ∈ R, SuppAt (G i).q.e (c.V j') r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit (G i).q).IsLoc ((G i).FY j' (b i) (hb i)) u uk ∧ uk ∈ (((G i).S.T (Fin D.R.t)).lev j' (b i) (hb i)).J ∧ xs i = r * u) → ∃ r ∈ R, r ∈ grpAt (c.V j') (· ∈ v.gP) ∧ ∃ k ∈ v.JG j', (List.ofFn xs).prod = r * k := by
  intro D c v n G hG j' hj R b hb xs H
  choose r hr hrs u uk hu huk hx using H
  have hne : ∀ i i', i ≠ i' → (G i).q.v ≠ (G i').q.v := fun i i' h e => h (hG.inj e)
  have hP : ∀ i, (G i).q.v ∈ v.gP := fun i => (hG.places _).2 ⟨i, rfl⟩
  have hus : ∀ i, SuppAt (G i).q.e (c.V j') (u i) := fun i => (hu i).1
  refine ⟨(List.ofFn r).prod, R.list_prod_mem ?_, Subgroup.list_prod_mem _ ?_, (List.ofFn u).prod,
    (hG.lev j' hj _).2 ⟨Subgroup.list_prod_mem _ ?_, ?_⟩, ?_⟩
  · rw [List.forall_mem_ofFn_iff]
    intro i
    exact hr i
  · rw [List.forall_mem_ofFn_iff]
    intro i
    exact mem_grpAt (G i).q (hrs i) (hP i)
  · rw [List.forall_mem_ofFn_iff]
    intro i
    exact mem_grpAt (G i).q (hus i) (hP i)
  · intro i a ha y hy
    obtain rfl : a = b i := by have := hb i; omega
    have e : matAt (G i).q (c.V j') (List.ofFn u).prod = matAt (G i).q (c.V j') (u i) := by
      rw [map_list_prod, List.map_ofFn]
      exact prod_ofFn_single _ i fun i' hi => map_eq_one (G i).q (G i').q (hne _ _ hi) (hus i')
    have e2 : ((G i).FY j' (b i) ha).β * y.val * ((G i).FY j' (b i) ha).γ =
        ((G i).FY j' (b i) ha).β * (uk i).val * ((G i).FY j' (b i) ha).γ := hy.symm.trans (e.trans (hu i).2)
    have e3 := congrArg (fun x => ((G i).FY j' (b i) ha).γ * x * ((G i).FY j' (b i) ha).β) e2
    simp only [← Matrix.mul_assoc, GlobalTheory.LocMod.Frame.γβ, Matrix.one_mul] at e3
    simp only [Matrix.mul_assoc, GlobalTheory.LocMod.Frame.γβ, Matrix.mul_one] at e3
    rw [Units.ext e3]
    exact huk i
  · rw [show xs = fun i => r i * u i from funext hx]
    exact prod_ofFn_mul r u fun i i' h => commute_of_suppAt (G i).q (G i').q (hne _ _ h.symm) (hus i) (hrs i')

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesSingleOrbitTamePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

open scoped TensorProduct

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.IwaOrbit

variable {D : D7}

theorem mul_mem_intAE {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem intAt_zero {P : Pl D → Prop} : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [(finPart D).map_zero]; exact zero_mem _⟩

theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) :
    a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [(finPart D).map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_mul {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) :
    a * b ∈ intAt D P :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [(finPart D).map_mul]; exact mul_mem_intAE ha.2 hb.2⟩

theorem mulVec_mem_intAt {P : Pl D → Prop} {m n : ℕ} {M : Matrix (Fin m) (Fin n) (AE D)} {z : Fin n → AE D}
    (hM : ∀ i j, M i j ∈ intAt D P) (hz : ∀ j, z j ∈ intAt D P) (i : Fin m) : (M *ᵥ z) i ∈ intAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_induction _ (· ∈ intAt D P) (fun _ _ => intAt_add) intAt_zero
    fun j _ => intAt_mul (hM i j) (hz j)

theorem mul_mem_idAt_left {P : Pl D → Prop} {l m n : ℕ} {A : Matrix (Fin l) (Fin m) (AE D)}
    (B : Matrix (Fin m) (Fin n) (AE D)) (hA : ∀ i j, A i j ∈ idAt D P) (i : Fin l) (j : Fin n) :
    (A * B) i j ∈ idAt D P := by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hA i k)

theorem mul_mem_idAt_right {P : Pl D → Prop} {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (AE D))
    {B : Matrix (Fin m) (Fin n) (AE D)} (hB : ∀ i j, B i j ∈ idAt D P) (i : Fin l) (j : Fin n) :
    (A * B) i j ∈ idAt D P := by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hB k j)

theorem smul_eq_self {P : Pl D → Prop} {ε : AE D} (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a) {m n : ℕ}
    {X : Matrix (Fin m) (Fin n) (AE D)} (hX : ∀ i j, X i j ∈ idAt D P) : ε • X = X := by
  ext i j; rw [Matrix.smul_apply, smul_eq_mul]; exact (hε _).1 (hX i j)

theorem smul_vec_eq_self {P : Pl D → Prop} {ε : AE D} (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a) {n : ℕ}
    {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D P) : ε • y = y := by
  funext i; rw [Pi.smul_apply, smul_eq_mul]; exact (hε _).1 (hy i)

theorem smul_mulVec' {m n : ℕ} (a : AE D) (A : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → AE D) :
    (a • A) *ᵥ y = a • (A *ᵥ y) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]

theorem adj_smul {m n : ℕ} (a : AE D) (X : Matrix (Fin m) (Fin n) (AE D)) : adj (a • X) = cA D a • adj X := by
  ext i j
  change cA D (a * X j i) = cA D a * cA D (X j i)
  exact (cA D).map_mul _ _

theorem adj_sub {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) (AE D)) : adj (X - Y) = adj X - adj Y := by
  ext i j
  change cA D (X j i - Y j i) = cA D (X j i) - cA D (Y j i)
  exact (cA D).map_sub _ _

theorem adj_mem_idAt {P : Pl D → Prop} {ε : AE D} (hcε : cA D ε = ε) (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a)
    {m n : ℕ} {X : Matrix (Fin m) (Fin n) (AE D)} (hX : ∀ i j, X i j ∈ idAt D P) (i : Fin n) (j : Fin m) :
    adj X i j ∈ idAt D P := by
  rw [hε]
  have h := congrArg (cA D) ((hε _).1 (hX j i))
  rw [(cA D).map_mul, hcε] at h
  exact h

theorem exists_onb (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)) (ht : Tame D v)
    (hεε : ε * ε = ε) (hcε : cA D ε = ε) (hεO : ε ∈ intAt D (· = v)) (hεI : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a)
    (hΛ : IsSDAt S v Λ) :
    ∃ b b' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, b i j ∈ idAt D (· = v)) ∧
      (∀ i j, b' i j ∈ idAt D (· = v)) ∧ b * b' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧
      b' * b = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧
      (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (b' *ᵥ y) i ∈ intAt D (· = v))) ∧
      adj b * (gA S * b) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  have adj_mul {l m n : ℕ} (X : Matrix (Fin l) (Fin m) (AE D)) (Y : Matrix (Fin m) (Fin n) (AE D)) : adj (X * Y) = adj Y * adj X := by
    ext i j
    change cA D ((X * Y) j i) = (adj Y * adj X) i j
    simp only [Matrix.mul_apply, map_sum, map_mul, GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply, mul_comm]
  obtain ⟨β, β', hβ, hβ', h1, h2, hmem, hHO, hHc, hH⟩ := _root_.GlobalTheory.IwaPlace.SDBasis.exists_basis_unimodular D S v ε Λ ht hεε hcε hεO hεI hΛ
  obtain ⟨P, P', hP, hP', hPP', hP'P, hPH⟩ := _root_.GlobalTheory.IwaPlace.UnimodNF.unimodular_congr_one D v ε S.rank _ ht hεε hcε hεO hεI hHO hHc hH
  refine ⟨β * P, P' * β', mul_mem_idAt_left P hβ, mul_mem_idAt_right P' hβ', ?_, ?_, ?_, ?_⟩
  · calc β * P * (P' * β') = β * (P * P') * β' := by simp only [Matrix.mul_assoc]
      _ = ε • (β * β') := by rw [hPP', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by rw [h1, smul_smul, hεε]
  · calc P' * β' * (β * P) = P' * (β' * β) * P := by simp only [Matrix.mul_assoc]
      _ = ε • (P' * P) := by rw [h2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by rw [hP'P, smul_smul, hεε]
  · intro y hy
    rw [hmem y hy]
    constructor
    · intro h i
      rw [← Matrix.mulVec_mulVec]
      exact mulVec_mem_intAt hP' h i
    · intro h i
      have hz : β' *ᵥ y = P *ᵥ (P' *ᵥ (β' *ᵥ y)) := by
        rw [Matrix.mulVec_mulVec, hPP', smul_mulVec', Matrix.one_mulVec,
          smul_vec_eq_self hεI (mulVec_mem_idAt β' hy)]
      rw [hz]
      exact mulVec_mem_intAt hP (fun j => by rw [Matrix.mulVec_mulVec]; exact h j) i
  · rw [adj_mul, ← hPH]
    simp only [Matrix.mul_assoc]

theorem selfDual_orbit : ∀ (D : D7) (S₀ : HSp D) (v : Pl D) (Λ Λ' : AddSubgroup (Fin S₀.rank → AE D)), Tame D v → IsSDAt S₀ v Λ → IsSDAt S₀ v Λ' → ∃ γ ∈ grpAt S₀ (· = v), ∀ y : Fin S₀.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ mt S₀ γ *ᵥ y ∈ Λ') := by
  intro D S v Λ Λ' ht hΛ hΛ'
  have adj_mul {l m n : ℕ} (X : Matrix (Fin l) (Fin m) (AE D)) (Y : Matrix (Fin m) (Fin n) (AE D)) : adj (X * Y) = adj Y * adj X := by
    ext i j
    change cA D ((X * Y) j i) = (adj Y * adj X) i j
    simp only [Matrix.mul_apply, map_sum, map_mul, GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply, mul_comm]
  obtain ⟨⟨ε, hεε, hcε, hεO, hεI, -⟩, -⟩ := _root_.GlobalTheory.FinPl.localComponents D (· = v)
  obtain ⟨b, b', hb, hb', hbb', hb'b, hmem, hG⟩ := exists_onb S v ε Λ ht hεε hcε hεO hεI hΛ
  obtain ⟨c, c', hc, hc', hcc', hc'c, hmem', hG'⟩ := exists_onb S v ε Λ' ht hεε hcε hεO hεI hΛ'
  set g := c * b' with hg
  have hgI : ∀ i j, g i j ∈ idAt D (· = v) := mul_mem_idAt_right c hb'
  have hag : ε • adj g = adj g := smul_eq_self hεI (adj_mem_idAt hcε hεI hgI)
  have hgg : ε • g = g := smul_eq_self hεI hgI
  have hb'b' : adj b' * b' = ε • gA S := by
    have h := congrArg (fun X => adj b' * X * b') hG
    rw [Matrix.mul_smul, Matrix.mul_one, smul_eq_self hεI (adj_mem_idAt hcε hεI hb')] at h
    rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← adj_mul, Matrix.mul_assoc, Matrix.mul_assoc, hbb', adj_smul,
      adj_one, hcε, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hεε]
  have hf1 : adj g * (gA S * g) = ε • gA S := by
    rw [hg, adj_mul]
    calc adj b' * adj c * (gA S * (c * b')) = adj b' * (adj c * (gA S * c)) * b' := by simp only [Matrix.mul_assoc]
      _ = ε • gA S := by rw [hG', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hb'b', smul_smul, hεε]
  have haG : adj g * gA S = ε • (adj g * gA S) := by rw [← Matrix.smul_mul, hag]
  have hGg : gA S * g = ε • (gA S * g) := by rw [← Matrix.mul_smul, hgg]
  have hunit : adj (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) * (gA S * (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D))))) = gA S := by
    show adj (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) * (gA S * (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D))))) = gA S
    rw [adj_add, adj_sub, adj_one, adj_smul, adj_one, hcε]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    rw [hf1]
    simp only [smul_add, smul_sub]
    rw [← haG, ← hGg, smul_smul, hεε]
    abel
  refine ⟨ofMat S (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) hunit, ?_, ?_⟩
  · refine (mem_congGrp_iff S (idAt D (· = v)) _).2 fun i j => ?_
    show (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idAt D (· = v)
    have e : (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j =
        g i j - ε * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
      rw [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact sub_mem (hgI i j) (Ideal.mul_mem_right _ _ hεO.1)
  · intro y hy
    have hMy : mt S (ofMat S (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) hunit) *ᵥ y = g *ᵥ y := by
      show (g + (1 - ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)))) *ᵥ y = g *ᵥ y
      rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, smul_mulVec', Matrix.one_mulVec,
        smul_vec_eq_self hεI hy, sub_self, add_zero]
    rw [hMy, hmem y hy, hmem' _ (mulVec_mem_idAt g hy)]
    have : c' *ᵥ (g *ᵥ y) = b' *ᵥ y := by
      rw [Matrix.mulVec_mulVec, hg, ← Matrix.mul_assoc, hc'c, Matrix.smul_mul, Matrix.one_mul,
        smul_eq_self hεI hb']
    rw [this]

end GlobalTheory.IwaOrbit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SkewAdjointSimilitudeExchangesHalves
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaHalf

variable {D : D7}

theorem isHalf_iff_smul {m n : ℕ} (e : AE D) (u : Mx D m n) : IsHalf e u ↔ e • u = u := by
  constructor
  · intro h; ext i j; rw [Matrix.smul_apply, smul_eq_mul, h i j]
  · intro h i j; have := congrFun (congrFun h i) j; rwa [Matrix.smul_apply, smul_eq_mul] at this

theorem isHalf_mul_left {k m n : ℕ} {e : AE D} (A : Mx D k m) {u : Mx D m n} (hu : IsHalf e u) :
    IsHalf e (A * u) := by
  rw [isHalf_iff_smul] at hu ⊢
  rw [← Matrix.mul_smul, hu]

theorem isHalf_mul_right {k m n : ℕ} {e : AE D} {u : Mx D k m} (B : Mx D m n) (hu : IsHalf e u) :
    IsHalf e (u * B) := by
  rw [isHalf_iff_smul] at hu ⊢
  rw [← Matrix.smul_mul, hu]

theorem isHalf_smul {m n : ℕ} {e : AE D} (c : AE D) {u : Mx D m n} (hu : IsHalf e u) :
    IsHalf e (c • u) := by
  rw [isHalf_iff_smul] at hu ⊢
  rw [smul_comm, hu]

theorem isHalf_adj_of_cA {m n : ℕ} {e : AE D} {z : Mx D m n} (hz : IsHalf (cA D e) z) :
    IsHalf e (adj z) := by
  intro i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  conv_lhs => rw [← GlobalTheory.DualPairCheck.cA_cA e]
  rw [← map_mul, hz j i]

theorem isHalf_cA_adj {m n : ℕ} {e : AE D} {z : Mx D m n} (hz : IsHalf e z) :
    IsHalf (cA D e) (adj z) := by
  intro i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  rw [← map_mul, hz j i]

theorem isHalf_ofAdj {L S : HSp D} {e : AE D} {z : Mx D L.rank S.rank} (hz : IsHalf e (adj z)) :
    IsHalf e (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S z) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  exact isHalf_smul _ (isHalf_mul_left _ (isHalf_mul_right _ hz))

theorem ofAdj_rat_mul_half : ∀ (D : D7) (L S L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (e : AE D) (y : WO S L''), (IsHalf (cA D e) y → IsHalf e (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * y))) ∧ (IsHalf e y → IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * y))) := by
  intro D L S L'' τ e y
  exact ⟨fun h => isHalf_ofAdj (isHalf_adj_of_cA (isHalf_mul_left _ h)),
    fun h => isHalf_ofAdj (isHalf_cA_adj (isHalf_mul_left _ h))⟩

end GlobalTheory.KappaHalf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFormHalfSkewAdjointImage
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KappaSplitPairing

theorem hO_ofAdj_right {D : D7} (L S : HSp D) (X : WO L S) (z : Mx D L.rank S.rank) :
    hO L S X (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S z) = incA D (D.host.xi0⁻¹) * (z ⬝ X).trace := by
  rw [hO_eq_trace, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]
  simp only [adj_smul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
    giA_gA_cancel, gA_giA_cancel, trace_smul, smul_eq_mul]
  rw [GlobalTheory.DualPairCheck.cA_incA, star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, neg_neg]

theorem map_trace {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {m : ℕ} (M : Mx D m m) : p.π M.trace = (M.map p.π).trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]

theorem key : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (L S L'' : HSp D) (ζ : Fin L.rank → D.host.E) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (s : k) (z₀ : Fin L''.rank → k), s ≠ 0 → τ.map p.pr *ᵥ z₀ = (-(p.xi * s)) • (fun i => p.pr (ζ i)) → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : Frame k S.rank n) (FL : Frame k L.rank Unit) (FL'' : Frame k L''.rank Unit), (∀ r, FL.β r () = s * p.pr (ζ r)) → (∀ r, FL''.β r () = z₀ r) → ∀ (x : Matrix Unit n k) (a : Matrix n Unit k), p.π (hO L S (p.up FL FS a) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * p.up FS FL'' x))) = -(∑ r, x () r * a r ()) := by
  intro D k _ _ _ _ p L S L'' ζ τ s z₀ hs hτ n _ _ FS FL FL'' hFL hFL'' x a
  rw [hO_ofAdj_right, map_mul, map_trace]
  have hxi : p.π (incA D D.host.xi0⁻¹) = p.xi⁻¹ := by
    change (p.π.comp (incA D)) D.host.xi0⁻¹ = ((p.π.comp (incA D)) D.host.xi0)⁻¹
    exact map_inv₀ _ _
  have hr : (rat τ : Mx D L.rank L''.rank).map p.π = τ.map p.pr := rfl
  have hu : ∀ {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
      (F₁ : Frame k S.rank Y') (F₂ : Frame k T.rank Y) (m : Matrix Y Y' k),
      (p.up F₁ F₂ m : Mx D T.rank S.rank).map p.π = F₂.β * m * F₁.γ := by
    intro Y Y' _ _ _ _ S T F₁ F₂ m
    ext i j
    exact p.π_ι _
  have hcol : τ.map p.pr * FL''.β = (-p.xi) • FL.β := by
    ext r u
    have h1 := congrFun hτ r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Matrix.mul_apply, hFL'', Matrix.smul_apply, smul_eq_mul, hFL, h1]
    ring
  have hγ : FL.γ * (τ.map p.pr * FL''.β) = (-p.xi) • (1 : Matrix Unit Unit k) := by
    rw [hcol, Matrix.mul_smul, FL.γβ]
  rw [hxi, Matrix.map_mul, Matrix.map_mul, hr, hu, hu]
  have e1 : τ.map p.pr * (FL''.β * x * FS.γ) * (FS.β * a * FL.γ) = (τ.map p.pr * FL''.β) * x * a * FL.γ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc FS.γ, FS.γβ, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hγ]
  have hx := Witness.xi_ne p
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
  simp only [Matrix.smul_apply, smul_eq_mul, neg_mul, Finset.sum_neg_distrib, mul_assoc, ← Finset.mul_sum, mul_neg,
    inv_mul_cancel_left₀ hx]

end GlobalTheory.KappaSplitPairing
end

