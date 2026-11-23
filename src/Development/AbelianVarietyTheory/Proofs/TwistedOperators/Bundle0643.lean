module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiDepthLatticeKeepsIsotropicHomPart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.SplitX

variable {D : D7}

private theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
  intro V Λ hΛ
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

theorem mem_of_latV_top {S : HSp D} {L : Lat S} (hL : Submodule.IsFullLattice D.host.E L) (r : Fin S.rank → D.host.E)
    (h : (fun i => pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * r i)) ∈ latV S L fun _ => True) : r ∈ L := by
  have h1 := GlobalTheory.LatVHat.latV_mem_hatL D S L _ _ h
  have e : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * r i)))) =
      fun i => Formalism.L2.Col.iA D.host.F D.host.E (r i) := by
    funext i
    rw [GlobalTheory.FinPlLoc.finPart_pair, one_mul]
    rfl
  rw [e] at h1
  let : Submodule.IsFullLattice D.host.E L := hL
  exact (GlobalTheory.CongStdLoc.incl_mem_hatL_iff (Submodule.IsLattice.fg D.host.E L) Submodule.IsFullLattice.span_eq_top r).1 h1

variable {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {L : Lat V} {L₀ : Lat V₀}

theorem proj_latV_at {v : GlobalTheory.FinPl.Pl D} (hm : MonoAt d L L₀ v) {y : Fin V.rank → AE D} (hy : y ∈ latV V L (· = v)) :
    rat (d.e * d.qX) *ᵥ y ∈ latV V L (· = v) := by
  have h := ((hm y).1 hy).1
  have e : rat (d.e * d.qX) *ᵥ y = ∑ i, GlobalTheory.FinPl.colMul d.jX i ((d.pX *ᵥ y) i) := by
    rw [show rat (d.e * d.qX) = d.jX ⬝ d.pX from rat_mul _ _, ← Matrix.mulVec_mulVec]
    funext k
    rw [Finset.sum_apply]
    simp only [GlobalTheory.FinPl.colMul, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact sum_mem fun i _ => h i

theorem proj_mem (hL : Submodule.IsFullLattice D.host.E L) (hm : ∀ v, MonoAt d L L₀ v) (x : Fin V.rank → D.host.E)
    (hx : x ∈ L) : (d.e * d.qX) *ᵥ x ∈ L := by
  apply mem_of_latV_top hL
  have hy : (fun i => pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * x i)) ∈ latV V L fun _ => True :=
    AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact (v.adicCompletionIntegers D.host.F).one_mem,
      fun v hv => (hv trivial).elim, 1, rfl, x, hx, rfl⟩
  have hz : rat (d.e * d.qX) *ᵥ (fun i => pairA D.host.F 0 (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 * x i)) ∈
      latV V L fun _ => True := by
    refine (GlobalTheory.FinPlLoc.part_lat _ V L _ hL.toIsLattice).2 ⟨fun i => mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy) i, fun v _ e he => ?_⟩
    rw [← Matrix.mulVec_smul]
    exact proj_latV_at d (hm v) (GlobalTheory.FinPlLoc.smul_latV v he hy)
  rwa [GlobalTheory.SeeSaw.SplitLat.rat_mulVec_gen] at hz

end GlobalTheory.AscFin.SplitX

namespace GlobalTheory.AscFin.SplitX

variable {D : D7}

theorem hatMx_mul {m n : ℕ} {M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)} (π : Matrix (Fin n) (Fin n) D.host.E)
    (hM : ∀ x ∈ M, x * π ∈ M) {z : Mx D m n} (hz : z ∈ hatMx M) : z ⬝ rat π ∈ hatMx M := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, x * π, hM x hx, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (pairA D.host.F 0 α ⊗ₜ[D.host.F] x i k) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] π k j) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.neg_mul]; exact neg_mem ha

theorem smul_homLat_mul {m n : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (π : Matrix (Fin n) (Fin n) D.host.E) (hπ : ∀ y ∈ Λ, π *ᵥ y ∈ Λ) :
    ∀ x ∈ I • homLat Λ Λ', x * π ∈ I • homLat Λ Λ' := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · rw [Matrix.smul_mul]
    refine Submodule.smul_mem_smul hr (fun y hy => ?_)
    rw [← Matrix.mulVec_mulVec]
    exact hn _ (hπ y hy)
  · rw [Matrix.add_mul]; exact add_mem hx hy

end GlobalTheory.AscFin.SplitX


open GlobalTheory.AscFin.SplitX in
theorem GlobalTheory.AscFin.SplitX.latRow_extX : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), (F.dJ (σ + 1) h).extX _ (u ⬝ (F.dJ (σ + 1) h).jX) ∈ latRow G (2 * σ + 2) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h u hu
  have hmono : ∀ v, MonoAt (F.dJ (σ + 1) h) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.core (2 * (σ + 1) + 1))) v :=
    fun v => (((_root_.GlobalTheory.AscFin.GridLat.lattices_grid D hq T L μ0 hL sc G W M hM F hF).2.1 (σ + 1) h).2.1 v).2
  have hV : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    (G.sp.V_is (2 * (σ + 1) + 1) 0 (by omega) (by omega) (Nat.zero_le _)).sd
  have hW : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.sp.V_is (2 * σ + 2) 0 (by omega) (by omega) (Nat.zero_le _)).sd
  have hπ := proj_mem (F.dJ (σ + 1) h) (selfDual_isFullLattice _ _ hV) hmono
  have hext : (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (u ⬝ (F.dJ (σ + 1) h).jX) =
      u ⬝ rat ((F.dJ (σ + 1) h).e * (F.dJ (σ + 1) h).qX) := by
    rw [HypDec.extX_apply, rat_mul, Matrix.mul_assoc]; rfl
  rw [hext]
  refine ⟨GlobalTheory.AscFinWit.latO_right (GlobalTheory.ChiGrid.isSelfDualC_neg hV) (GlobalTheory.ChiGrid.isSelfDualC_neg hV) hW _ hπ hu.1,
    fun e he => ?_⟩
  rw [← Matrix.smul_mul]
  exact hatMx_mul _ (smul_homLat_mul _ _ hπ) (hu.2 e he)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiStepCoreComponentMemCoreDepthLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CoreComp

variable {D : D7}

def finV {n : ℕ} (z : Fin n → D.host.E) : Fin n → AE D := fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i

theorem rat_entry {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (i : Fin m) (j : Fin n) :
    (rat A : Mx D m n) i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] A i j := rfl

theorem rat_mulVec_finV {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (z : Fin n → D.host.E) :
    (rat A : Mx D m n) *ᵥ finV z = finV (A *ᵥ z) := by
  funext i
  simp only [finV, mulVec, dotProduct, TensorProduct.tmul_sum, rat_entry, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem finV_mem {S : HSp D} {L : Lat S} {z : Fin S.rank → D.host.E} (hz : z ∈ L) :
    finV z ∈ latV S L (fun _ => True) :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, fun v hv => absurd trivial hv, 1, rfl, z, hz,
    by funext i; simp [finV]⟩

theorem mem_of_finV (S : HSp D) (L : Lat S) (hL : Submodule.IsFullLattice D.host.E L) (z : Fin S.rank → D.host.E)
    (hz : finV z ∈ latV S L (fun _ => True)) : z ∈ L :=
  GlobalTheory.RatLat.mem_of_mem_latV D S L hL z hz

theorem loc_iff {S : HSp D} {L : Lat S} (hL : Submodule.IsLattice D.host.E L) (y : Fin S.rank → AE D) :
    y ∈ latV S L (fun _ => True) ↔ (∀ i, y i ∈ idAt D (fun _ => True)) ∧
      ∀ v, ∀ e ∈ intAt D (· = v), e • y ∈ latV S L (· = v) := by
  have := ((GlobalTheory.FinPl.localComponents D (fun _ => True)).2 S).2.2.2 L y hL
  simpa using this

end GlobalTheory.CoreComp

namespace GlobalTheory.CoreComp

variable {D : D7}

theorem mulVec_mem_idAt {m n : ℕ} (M : Mx D m n) {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D (fun _ => True)) (i : Fin m) :
    (M *ᵥ y) i ∈ idAt D (fun _ => True) := mulVec_idAt M hy i

theorem witt_core_inclusion_maps_split_lattices {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : Submodule.IsFullLattice D.host.E L) (hL₀ : Submodule.IsLattice D.host.E L₀) (hM : ∀ v, MonoAt d L L₀ v)
    {z : Fin S₀.rank → D.host.E} (hz : z ∈ L₀) : d.i₀ *ᵥ z ∈ L := by
  apply mem_of_finV S L hL
  rw [← rat_mulVec_finV]
  have hz' := (loc_iff hL₀ _).1 (finV_mem hz)
  refine (loc_iff hL.toIsLattice _).2 ⟨mulVec_mem_idAt _ hz'.1, fun v e he => ?_⟩
  have h1 := hz'.2 v e he
  rw [← Matrix.mulVec_smul]
  refine (hM v _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have e0 : (d.pX *ᵥ ((rat d.i₀ : Mx D S.rank S₀.rank) *ᵥ e • finV z)) i = 0 := by
      rw [Matrix.mulVec_mulVec, show (rat d.i₀ : Mx D S.rank S₀.rank) = d.j0 from rfl, HypDec.pX_j0, Matrix.zero_mulVec]; rfl
    rw [e0]
    have : GlobalTheory.FinPl.colMul d.jX i 0 = 0 := by funext k; simp [GlobalTheory.FinPl.colMul]
    rw [this]; exact zero_mem _
  · have e0 : (d.pY *ᵥ ((rat d.i₀ : Mx D S.rank S₀.rank) *ᵥ e • finV z)) i = 0 := by
      rw [Matrix.mulVec_mulVec, show (rat d.i₀ : Mx D S.rank S₀.rank) = d.j0 from rfl, HypDec.pY_j0, Matrix.zero_mulVec]; rfl
    rw [e0]
    have : GlobalTheory.FinPl.colMul d.jY i 0 = 0 := by funext k; simp [GlobalTheory.FinPl.colMul]
    rw [this]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, show (rat d.i₀ : Mx D S.rank S₀.rank) = d.j0 from rfl, HypDec.p0_j0, Matrix.one_mulVec]
    exact h1

theorem witt_core_projection_maps_split_lattices {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : Submodule.IsLattice D.host.E L) (hL₀ : Submodule.IsFullLattice D.host.E L₀) (hM : ∀ v, MonoAt d L L₀ v)
    {y : Fin S.rank → D.host.E} (hy : y ∈ L) : d.q0 *ᵥ y ∈ L₀ := by
  apply mem_of_finV S₀ L₀ hL₀
  rw [← rat_mulVec_finV]
  have hy' := (loc_iff hL _).1 (finV_mem hy)
  refine (loc_iff hL₀.toIsLattice _).2 ⟨mulVec_mem_idAt _ hy'.1, fun v e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact ((hM v _).1 (hy'.2 v e he)).2.2

theorem qA_maps {S A B : HSp D} (o : OrthDec S A B) {L : Lat S} {LA : Lat A} {LB : Lat B}
    (hL : Submodule.IsLattice D.host.E L) (hLA : Submodule.IsFullLattice D.host.E LA) (hO : ∀ v, OrthAt o L LA LB v)
    {y : Fin S.rank → D.host.E} (hy : y ∈ L) : o.qA *ᵥ y ∈ LA := by
  apply mem_of_finV A LA hLA
  rw [← rat_mulVec_finV]
  have hy' := (loc_iff hL _).1 (finV_mem hy)
  refine (loc_iff hLA.toIsLattice _).2 ⟨mulVec_mem_idAt _ hy'.1, fun v e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact ((hO v _).1 (hy'.2 v e he)).1

theorem rat_mulVec_mem_latA {S T : HSp D} (m : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {L : Lat S} {L' : Lat T}
    (h : ∀ x ∈ L, m *ᵥ x ∈ L') {P : GlobalTheory.FinPl.Pl D → Prop} {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) :
    (rat m : Mx D T.rank S.rank) *ᵥ y ∈ latA T L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hα', a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨α, hα, hα', a, ha, m *ᵥ x, h x hx, ?_⟩
    funext i
    simp only [mulVec, dotProduct, Finset.mul_sum, TensorProduct.tmul_sum, rat_entry, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1; ring
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [mulVec_neg]; exact neg_mem hx

theorem latO_sandwich {S T S' T' : HSp D} {ΛS : Lat S} {ΛT : Lat T} {ΛS' : Lat S'} {ΛT' : Lat T'}
    (M : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (N : Matrix (Fin S.rank) (Fin S'.rank) D.host.E)
    (hS : IsSelfDualC S ΛS) (hS' : IsSelfDualC S' ΛS') (hT' : IsSelfDualC T' ΛT')
    (hN : ∀ y ∈ ΛS', N *ᵥ y ∈ ΛS) (hM : ∀ y ∈ ΛT, M *ᵥ y ∈ ΛT') {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) :
    ((rat M : Mx D T'.rank T.rank) * u * (rat N : Mx D S.rank S'.rank) : WO S' T') ∈
      latO S' T' (ΛS' : Set _) (ΛT' : Set _) fun _ => True := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S' T' ΛS' ΛT' hS' hT']
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · simp only [Matrix.mul_apply]
    exact sum_mem fun l _ => Ideal.mul_mem_right _ _
      (sum_mem fun k _ => Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu k l))
  · show ((rat M : Mx D T'.rank T.rank) * u * (rat N : Mx D S.rank S'.rank)) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact rat_mulVec_mem_latA M hM
      (GlobalTheory.FinPl.LatMem.latO_maps hS hu (GlobalTheory.OrthSumLat.rat_mulVec_mem_latV N hN hy))

theorem hatMx_sandwich {S T S' T' : HSp D} {ΛS : Lat S} {ΛT : Lat T} {ΛS' : Lat S'} {ΛT' : Lat T'}
    (M : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (N : Matrix (Fin S.rank) (Fin S'.rank) D.host.E)
    (hN : ∀ y ∈ ΛS', N *ᵥ y ∈ ΛS) (hM : ∀ y ∈ ΛT, M *ᵥ y ∈ ΛT') (I : Ideal (𝓞 D.host.E))
    {z : Mx D T.rank S.rank} (hz : z ∈ hatMx (I • homLat ΛS ΛT)) :
    (rat M : Mx D T'.rank T.rank) * z * (rat N : Mx D S.rank S'.rank) ∈ hatMx (I • homLat ΛS' ΛT') := by
  have key : ∀ X ∈ I • homLat ΛS ΛT, M * X * N ∈ I • homLat ΛS' ΛT' := by
    intro X hX
    refine Submodule.smul_induction_on hX (fun r hr Y hY => ?_) (fun a b ha hb => ?_)
    · have e : M * (r • Y) * N = r • (M * Y * N) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      rw [e]
      refine Submodule.smul_mem_smul hr ?_
      intro y hy
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact hM _ (hY _ (hN y hy))
    · rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem ha hb
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, X, hX, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, M * X * N, key X hX, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul, TensorProduct.tmul_sum, rat_entry,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem hx

end GlobalTheory.CoreComp

namespace GlobalTheory.CoreComp

theorem core_mem_latCore : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∀ u ∈ (pcFB W F σ h h').Γ₀, ((F.oB σ h').resT _ u).1 ∈ latCore G (2 * σ + 2) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h' u hu
  have I := _root_.GlobalTheory.AscFin.GridLat.lattices_grid D hq T L μ0 hL sc G W M hM F hF
  have sd : ∀ X : Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → IsSelfDualC (G.V X) (G.Λ X) :=
    fun X h1 h2 => (G.isV h1 h2).sd
  have sdG3 : IsSelfDualC (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) :=
    sd _ ⟨by omega, Nat.zero_le _⟩ (fun j e => by cases e)
  have sdG2 : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    sd _ ⟨h', Nat.zero_le _⟩ (fun j e => by cases e)
  have sdC3 : IsSelfDualC (G.V (.core (2 * σ + 2 + 1))) (G.Λ (.core (2 * σ + 2 + 1))) :=
    sd (.core (2 * σ + 2 + 1)) (show 2 * σ + 2 + 1 ≤ D.R.m by omega) (fun j e => by cases e)
  have sdC2 : IsSelfDualC (G.V (.core (2 * σ + 2))) (G.Λ (.core (2 * σ + 2))) :=
    sd (.core (2 * σ + 2)) (show 2 * σ + 2 ≤ D.R.m by omega) (fun j e => by cases e)
  have sd0 : IsSelfDualC (F.V₀ σ) (lat0 F σ h') := (I.2.1 σ h').1
  have hMJ : ∀ v, MonoAt (F.dJ (σ + 1) h) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.core (2 * (σ + 1) + 1))) v :=
    fun v => ((I.2.1 (σ + 1) h).2.1 v).2
  have hMB : ∀ v, MonoAt (F.dB σ h') (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v := fun v => ((I.2.1 σ h').2.1 v).1
  have hOB := (I.2.1 σ h').2.2.2

  have fullG3 := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sdG3
  have fullC2 := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sdC2
  have full0 := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sd0
  have hN : ∀ y ∈ G.Λ (.core (2 * σ + 2 + 1)), (F.dJ (σ + 1) h).i₀ *ᵥ y ∈ G.Λ (.grid (2 * σ + 2 + 1) 0) :=
    fun y hy => witt_core_inclusion_maps_split_lattices (F.dJ (σ + 1) h) fullG3 sdC3.1 hMJ hy
  have hMm : ∀ y ∈ G.Λ (.grid (2 * σ + 2) 0),
      ((F.oB σ h').qA * (F.dB σ h').q0) *ᵥ y ∈ G.Λ (.core (2 * σ + 2)) := fun y hy => by
    rw [← Matrix.mulVec_mulVec]
    exact qA_maps (F.oB σ h') sd0.1 fullC2 hOB
      (witt_core_projection_maps_split_lattices (F.dB σ h') sdG2.1 full0 hMB hy)
  have hx := AddSubgroup.mem_comap.1 hu
  set x := ((F.dJ (σ + 1) h).ext0 _).comp ((F.dB σ h').inc0 _) u with hxdef
  have hc : ((F.oB σ h').resT _ u).1 =
      (rat ((F.oB σ h').qA * (F.dB σ h').q0) : Mx D _ _) * x * (rat (F.dJ (σ + 1) h).i₀ : Mx D _ _) := by
    rw [OrthDec.resT_apply, rat_mul, hxdef]
    change (F.oB σ h').pA * u = (F.oB σ h').pA * (F.dB σ h').p0 * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) *
      (F.dJ (σ + 1) h).j0
    have e1 : (F.dB σ h').p0 * (F.dB σ h').j0 = 1 := HypDec.p0_j0 _
    have e2 : (F.dJ (σ + 1) h).p0 * (F.dJ (σ + 1) h).j0 = 1 := HypDec.p0_j0 _
    calc (F.oB σ h').pA * u = (F.oB σ h').pA * (((F.dB σ h').p0 * (F.dB σ h').j0) * u *
          ((F.dJ (σ + 1) h).p0 * (F.dJ (σ + 1) h).j0)) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hc]
  refine ⟨?_, fun e he => ?_⟩
  · exact latO_sandwich _ _ (isSelfDualC_neg sdG3) (isSelfDualC_neg sdC3) sdC2 hN hMm hx.1
  · rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    exact hatMx_sandwich _ _ hN hMm _ (hx.2 e he)

end GlobalTheory.CoreComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastBiExpand
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.LastSeeSawGen.lastBi_expand : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → GlobalTheory.SplitWeil.HasConductor ψk 1 → ∀ (ρ : ℕ) (B : GlobalTheory.Unf.BesLev D ρ) (W X T L'' : HSp D) (o'' : OrthDec X T L'') (τ : Matrix (Fin B.L.rank) (Fin L''.rank) D.host.E), L''.rank = 1 → τᴴ * (B.L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (a : k) (z₀ : Fin L''.rank → k), a ≠ 0 → τ.map p.pr *ᵥ z₀ = (-(p.xi * a)) • (fun i => p.pr (B.ζ i)) → ∀ (n : Type) [Fintype n] [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (Z : Type) [Fintype Z] [DecidableEq Z] (FA : GlobalTheory.LocMod.Frame k B.A.rank n') (F₀ : GlobalTheory.LocMod.Frame k B.V₀.rank (n' ⊕ Unit)) (FS : GlobalTheory.LocMod.Frame k W.rank n) (FT : GlobalTheory.LocMod.Frame k T.rank Z) (FX : GlobalTheory.LocMod.Frame k X.rank (Z ⊕ Unit)), p.IsCoreFrame B a FA F₀ → FX.β = fromCols (o''.iA.map p.pr * FT.β) (Matrix.of fun r _ => (o''.iB.map p.pr *ᵥ z₀) r) → ∀ T₁ T₂, p.IsModel ψ F₀ FS T₁ → p.IsModel ψ FS FT T₂ → ∀ Φ₁ Φ₂ O₁ O₂, GlobalTheory.LocMod.IsOne O₁ → GlobalTheory.LocMod.IsOne O₂ → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (Ξ₁ : I → GlobalTheory.SplitWeil.SB (Matrix n n' k)) (Ξ₂ : I → GlobalTheory.SplitWeil.SB (Matrix (Z ⊕ Unit) n k)) (c₁ : I → WO B.A W →₀ ℂ) (c₂ : I → WO W X →₀ ℂ), (∀ i ∈ S, p.IsCombAt ψ FA FS (c₁ i) (Ξ₁ i).1 ∧ p.IsCombAt ψ FS FX (c₂ i) (Ξ₂ i).1) → (∀ (y : Matrix n n' k) (y' : Matrix (Z ⊕ Unit) n k), Φ₂.1 y'.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun u => Φ₁.1 (fromCols y (Matrix.of fun r _ => u r))) (y' (Sum.inr ())) = ∑ i ∈ S, x i * ((Ξ₁ i).1 y * (Ξ₂ i).1 y')) → GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ Φ₁) (T₂ Φ₂) = ∑ i ∈ S, x i • biComb ψ B.A W X (c₁ i) (c₂ i) (GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ O₁) (T₂ O₂)) := by
  classical
  intro D k _ _ _ _ _ _ ν hν p ψ hstd ψk hchar hcond ρ B W X T L'' o'' τ hL hτ a z₀ ha hz n _ _ n' _ _ Z _ _
    FA F₀ FS FT FX hcore hFX T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hO₁ hO₂ I S x Ξ₁ Ξ₂ c₁ c₂ hc hrel
  have := hν.1
  obtain ⟨Λ, hΛ, hK⟩ := GlobalTheory.LastKerLoc.lastLoc D k p ν hν.1 ψ hstd ψk hchar ρ B W X T L'' o'' τ hL hτ a z₀ ha hz
    n n' Z FA F₀ FS FT FX hcore hFX T₁ T₂ hT₁ hT₂
  obtain ⟨Ξ, hΞ, hΞK⟩ := hK Φ₁ Φ₂
  obtain ⟨Ξ', hΞ', hΞ'K⟩ := hK O₁ O₂
  have hv1 : valuation k (-1 : k) = 1 := by simp
  haveI : T2Space (Matrix n n' k) := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField
  haveI : T2Space (Matrix (Z ⊕ Unit) n k) := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField
  let P : I → SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k) := fun i =>
    ⟨fun q => (Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2,
      GlobalTheory.FinPl.Comm.prod_mem_SB (Ξ₁ i).2 (Ξ₂ i).2 continuous_fst continuous_snd continuous_id fun _ => rfl⟩
  let O₁' : SB (Matrix n n' k) := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
  let O₂' : SB (Matrix (Z ⊕ Unit) n k) := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
  have hone : ∀ q, Ξ'.1 q = O₁'.1 q.1 * O₂'.1 q.2 := fun q => by
    rw [hΞ' q, hO₂]
    have e : (fun y => O₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]}
          (fun _ => (1 : ℂ)) q.1 * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk 0) y := by
      funext y
      rw [hO₁]
      exact GlobalTheory.LastTwoSteps.intInd_fromCols q.1 y
    rw [e, GlobalTheory.LastTwoSteps.hat_const_mul, GlobalTheory.LastTwoSteps.hat_int hcond hν hv1]
    simp only [O₁', O₂']
    rw [GlobalTheory.LastTwoSteps.intInd_rows q.2]
    ring
  have hsum : Ξ = ∑ i ∈ S, x i • P i := by
    apply Subtype.ext
    funext q
    rw [hΞ q, hrel q.1 q.2, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have key : ∀ i ∈ S, Λ (P i) = biComb ψ B.A W X (c₁ i) (c₂ i) (Λ Ξ') := fun i hi =>
    (GlobalTheory.BiComb.comb_bimodel_and_line D k p ψ n n' (Z ⊕ Unit)).1 B.A W X FA FS FX Λ (c₁ i) (c₂ i) (Ξ₁ i) O₁'
      (Ξ₂ i) O₂' (P i) Ξ' hΛ (hc i hi).1 (hc i hi).2 rfl rfl (fun _ => rfl) hone
  have e1 : GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ Φ₁) (T₂ Φ₂) = Λ Ξ := funext fun u => hΞK u
  have e2 : GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ O₁) (T₂ O₂) = Λ Ξ' := funext fun u => hΞ'K u
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, e2, hsum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, key i hi]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFinitePointsOfHasLocalLatticeMatrices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowCover

theorem mem_GfC_of_hasLoc : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x : GA D (G.V (.grid D.R.m j)))
    (g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → x ∈ GfC _ := by
  intro D T L sc G t B j hj x g hx
  obtain ⟨e, ⟨⟨es, hes, rfl⟩, -⟩, hg, -⟩ := hx
  have h0 : infPart D ((∑ PP ∈ locPl G t, es PP) + cA D (∑ PP ∈ locPl G t, es PP)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum (cA D), ← Finset.sum_add_distrib, map_sum]
    refine Finset.sum_eq_zero fun PP hPP => ?_
    obtain ⟨-, -, v, ε, ⟨α, rfl, -⟩, h⟩ := (hes PP hPP).1
    rw [h]; exact TensorProduct.zero_tmul _ _
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := congrArg (infPart D) (hg i j)
  rw [map_mul, h0, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero] at this
  refine Eq.trans this ?_
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end GlobalTheory.RowCover
end
end

