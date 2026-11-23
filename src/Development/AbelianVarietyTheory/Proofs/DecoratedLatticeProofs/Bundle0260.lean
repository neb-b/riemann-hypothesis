module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameRescaleConjReductionsDiagonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ExistsBaseRingOfConjugationFixedTensor
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0250

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDiagonalFrameChangeUnweightingSymEdges
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagFrameWeights

theorem isUnit_res {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) (x : Formalism.L2.DIV.kP PP) (hx : x ≠ 0) :
    IsUnit x := by
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  letI : Field (Formalism.L2.DIV.kP PP) := Ideal.Quotient.field PP.asIdeal
  exact isUnit_iff_ne_zero.mpr hx


set_option maxHeartbeats 1000000 in
theorem exists_diag_frame : ∀ {D : D7} {n : ℕ} (ρ k : ℕ) (Pg : Finset (Pl D.host.E)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β₀ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)), Formalism.L2.DIV.IsFrame β₀ Λ → ∀ a : ∀ PP : Pl D.host.E, Fin n → Fin n → kP PP, (∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → a PP i j ≠ 0) → ∃ β₃ : GL (Fin n) (Formalism.IndefR.Lev.EAf D), Formalism.L2.DIV.IsFrame β₃ Λ ∧ Formalism.L2.DIV.St β₃ = Formalism.L2.DIV.St β₀ ∧ ∀ PP ∈ Pg, ∀ y ∈ Formalism.L2.DIV.St β₀, (Formalism.L2.DIV.redFn β₃ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k ↔ Formalism.L2.DIV.redFn β₀ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k) ∧ (∑ i, ∑ j, if Formalism.L2.DIV.symEdge ρ k i j then a PP i j * ((Formalism.L2.DIV.redFn β₀ PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j else 0) = Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge ρ k) (Formalism.L2.DIV.redFn β₃ PP y) := by
  intro D n ρ k Pg Λ β₀ hβ a ha
  classical
  let w : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → Fin n → (Formalism.L2.DIV.kP PP)ˣ := fun PP i j =>
    if h : PP ∈ Pg ∧ Formalism.L2.DIV.symEdge ρ k i j then (isUnit_res PP (a PP i j) (ha PP h.1 i j h.2)).unit else 1
  let d : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → (Formalism.L2.DIV.kP PP)ˣ := fun PP =>
    GlobalTheory.SeeConjScale.forestLift (Formalism.L2.DIV.symEdge ρ k) (GlobalTheory.SeeConjScale.symEdge_lt ρ k) (w PP)
  have hd : ∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → (((d PP i)⁻¹ : (Formalism.L2.DIV.kP PP)ˣ) : Formalism.L2.DIV.kP PP) * (d PP j : Formalism.L2.DIV.kP PP) = a PP i j := by
    intro PP hPP i j h
    have e := congrArg Units.val (GlobalTheory.SeeConjScale.forestLift_edge (Formalism.L2.DIV.symEdge ρ k) (GlobalTheory.SeeConjScale.symEdge_lt ρ k)
      (GlobalTheory.SeeConjScale.symEdge_uniq ρ k) (w PP) h)
    rw [Units.val_mul] at e
    rw [e]
    simp only [w, dif_pos (And.intro hPP h), IsUnit.unit_spec]
  have hex : ∀ j : Fin n, ∃ u : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ,
      ∀ PP ∈ Pg, Formalism.L2.DIV.resS D.host.F PP u = d PP j :=
    fun j => GlobalTheory.FrameRescale.exists_unit_res (D := D) Pg (fun PP => d PP j)
  choose u hu using hex
  have hSt : ∀ M, M ∈ Formalism.L2.DIV.St (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) ↔ M ∈ Formalism.L2.DIV.St β₀ := by
    intro M
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨GlobalTheory.SeeConjRead.diagGL u * y * (GlobalTheory.SeeConjRead.diagGL u)⁻¹, (GlobalTheory.FrameRescale.frGL_mul β₀ (GlobalTheory.SeeConjRead.diagGL u) y).symm⟩
    · rintro ⟨y, rfl⟩
      refine ⟨(GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u, ?_⟩
      rw [GlobalTheory.FrameRescale.frGL_mul]
      congr 1
      group
  have hred : ∀ PP ∈ Pg, ∀ M ∈ Formalism.L2.DIV.St β₀,
      Formalism.L2.DIV.redFn (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) PP M =
        (GlobalTheory.SeeConjRead.diagGL (d PP))⁻¹ * Formalism.L2.DIV.redFn β₀ PP M * GlobalTheory.SeeConjRead.diagGL (d PP) := by
    intro PP hPP M hM
    obtain ⟨y, rfl⟩ := hM
    have e1 : Formalism.L2.DIV.frGL β₀ y =
        Formalism.L2.DIV.frGL (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) ((GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u) := by
      rw [GlobalTheory.FrameRescale.frGL_mul]
      congr 1
      group
    have hb : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) (GlobalTheory.SeeConjRead.diagGL u) = GlobalTheory.SeeConjRead.diagGL (d PP) := by
      apply Units.ext
      ext i j
      show Formalism.L2.DIV.resS D.host.F PP (((GlobalTheory.SeeConjRead.diagGL u : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) i j) =
        ((GlobalTheory.SeeConjRead.diagGL (d PP) : GL (Fin n) (Formalism.L2.DIV.kP PP)) : Matrix (Fin n) (Fin n) (Formalism.L2.DIV.kP PP)) i j
      rw [GlobalTheory.SeeConjRead.diagGL_val, GlobalTheory.SeeConjRead.diagGL_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
      split_ifs with h
      · subst h
        exact hu i PP hPP
      · exact map_zero _
    have e3 := Formalism.L2.DIV.redFn_frGL (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) PP ((GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u)
    have e4 := Formalism.L2.DIV.redFn_frGL β₀ PP y
    rw [← e1] at e3
    rw [e3, e4, GlobalTheory.FrameRescale.bc_conj, hb]
  refine ⟨β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u), ?_, ?_, ?_⟩
  · intro x
    rw [hβ x]
    have hinv : ((β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u))⁻¹).val = Matrix.diagonal (fun i => ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D)) *
          (β₀⁻¹).val := by
      rw [_root_.mul_inv_rev, Units.val_mul, ← map_inv, GlobalTheory.SeeConjRead.diagGL_inv, GlobalTheory.FrameRescale.intGL_diagGL_val]
    rw [hinv]
    refine forall_congr' fun i => ?_
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    have hm : ((u i : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D) * ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D) = 1 := congrArg Subtype.val (u i).mul_inv
    constructor
    · intro h
      exact Subring.mul_mem _ ((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ).val.2 h
    · intro h
      have h2 := Subring.mul_mem _ (u i).val.2 h
      rwa [← mul_assoc, hm, one_mul] at h2
  · ext M
    exact hSt M
  · intro PP hPP y hy
    rw [hred PP hPP y hy]
    refine ⟨(GlobalTheory.SeeConjRead.unipSym_conj_iff ρ k (d PP) _).symm, ?_⟩
    unfold Formalism.L2.DIV.edgeSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [GlobalTheory.SeeConjRead.diagGL_conj_apply, ← hd PP hPP i j h]
      ring
    · rfl

end GlobalTheory.DiagFrameWeights
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHermIsUnitGeneric
section
noncomputable section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HermTransversal

theorem isUnit_glue {R ι : Type} [CommRing R] [Fintype ι] {n : ℕ} (e t : ι → R)
    (A : ι → Matrix (Fin n) (Fin n) R) (h1 : ∑ i, e i = 1) (ho : ∀ i j, i ≠ j → e i * e j = 0)
    (ht : ∀ i, t i * (A i).det = e i) : IsUnit (∑ i, e i • A i) := by
  classical
  have hee : ∀ i, e i * e i = e i := fun i => by
    have : e i * ∑ j, e j = e i * e i := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_single i (fun j _ hj => ho i j (Ne.symm hj)) (by simp)
    rw [← this, h1, mul_one]
  have hs : ∀ i, e i • (∑ j, e j • A j) = e i • A i := fun i => by
    rw [Finset.smul_sum, Finset.sum_eq_single i]
    · rw [smul_smul, hee]
    · intro j _ hj
      rw [smul_smul, ho i j (Ne.symm hj), zero_smul]
    · simp
  have hB : (∑ i, e i • A i) * (∑ j, (t j * e j) • (A j).adjugate) = 1 := by
    rw [Finset.mul_sum]
    have : ∀ j, (∑ i, e i • A i) * ((t j * e j) • (A j).adjugate) = e j • (1 : Matrix (Fin n) (Fin n) R) := fun j => by
      rw [Matrix.mul_smul, mul_smul, ← Matrix.smul_mul (e j), hs, Matrix.smul_mul, Matrix.mul_adjugate, smul_smul,
        smul_smul]
      congr 1
      rw [mul_right_comm, ht, hee]
    simp only [this]
    rw [← Finset.sum_smul, h1, one_smul]
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hB)

section Generic

variable {E R : Type} [Field E] [CharZero E] [CommRing R] {n : ℕ}

theorem exists_herm_notMem (σ : E →+* E) (δ : E) (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (ι : E →+* R) (τ : R →+* R)
    (hτι : ∀ z, τ (ι z) = ι (σ z)) (c d p q : Matrix (Fin n) (Fin n) R) (h : c * p + d * q = 1) (M : Ideal R)
    (hM : M.IsMaximal) :
    ∃ x : Matrix (Fin n) (Fin n) E, (∀ i j, σ (x i j) = x j i) ∧
      (c * x.map ι + d).det * τ (c * x.map ι + d).det ∉ M := by
  letI := Ideal.Quotient.field M
  let π₀ : R →+* R ⧸ M := Ideal.Quotient.mk M
  let φ : E →+* R ⧸ M := π₀.comp ι
  let π := π₀.mapMatrix (m := Fin n)
  let ψ := (π₀.comp τ).mapMatrix (m := Fin n)
  have h1 : π c * π p + π d * π q = 1 := by rw [← map_mul, ← map_mul, ← map_add (f := _), h, map_one]
  have h2 : ψ c * ψ p + ψ d * ψ q = 1 := by rw [← map_mul, ← map_mul, ← map_add (f := _), h, map_one]
  obtain ⟨y, hy⟩ := GlobalTheory.T.matrix_field_stableRange_one_det_ne_zero _ n _ _ _ _ h1
  obtain ⟨y', hy'⟩ := GlobalTheory.T.matrix_field_stableRange_one_det_ne_zero _ n _ _ _ _ h2
  obtain ⟨x, hxs, hx1, hx2⟩ := _root_.GlobalTheory.exists_hermitian_det_ne_zero_two E (R ⧸ M) σ φ δ hδ hσδ n _ _ _ _ _ _ hy hy'
  have hx : ∀ i j, σ (x i j) = x j i := fun i j => congrFun (congrFun hxs i) j
  refine ⟨x, hx, fun hmem => ?_⟩
  rcases hM.isPrime.mem_or_mem hmem with h' | h'
  · apply hx1
    have e : π₀ (c * x.map ι + d).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h'
    rw [RingHom.map_det] at e
    change (π (c * x.map ι + d)).det = 0 at e
    rw [map_add (f := _), map_mul] at e
    exact e
  · apply hx2
    have e : (π₀.comp τ) (c * x.map ι + d).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h'
    rw [RingHom.map_det] at e
    change (ψ (c * x.map ι + d)).det = 0 at e
    rw [map_add (f := _), map_mul] at e
    have e2 : ψ (x.map ι) = x.transpose.map φ := by
      funext i j
      change π₀ (τ (ι (x i j))) = π₀ (ι (x j i))
      rw [hτι, hx]
    rw [e2] at e
    exact e

theorem exists_herm_isUnit_generic {A : Type} [CommRing A] (σ : E →+* E) (δ : E) (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (ι : E →+* R) (τ : R →+* R) (hτι : ∀ z, τ (ι z) = ι (σ z)) (hττ : ∀ z, τ (τ z) = z)
    (a : A →+* R) (ha : Function.Injective a) (hτa : ∀ z, τ (a z) = a z) (hfix : ∀ y, τ y = y → ∃ z, a z = y)
    (k : A) (hk : k * 2 = 1)
    (hid : ∀ (κ : Type) [Fintype κ] (f s : κ → A), ∑ i, s i * f i = 1 → ∃ e t : κ → A,
      ∑ i, e i = 1 ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧ ∀ i, t i * f i = e i)
    (c d p q : Matrix (Fin n) (Fin n) R) (h : c * p + d * q = 1) :
    ∃ x : Matrix (Fin n) (Fin n) R, (x.map τ)ᵀ = x ∧ IsUnit (c * x + d) := by
  classical
  let H := {x : Matrix (Fin n) (Fin n) E // ∀ i j, σ (x i j) = x j i}
  let u : H → R := fun x => (c * x.1.map ι + d).det
  let f : H → R := fun x => u x * τ (u x)
  have htop : Ideal.span (Set.range f) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨x, hx, hn⟩ := exists_herm_notMem σ δ hδ hσδ ι τ hτι c d p q h M hM
    exact hn (hle (Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩))
  have h1 : (1 : R) ∈ Submodule.span R (Set.range f) := (Ideal.eq_top_iff_one _).1 htop
  obtain ⟨C, hC⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h1
  have hC' : ∑ i : C.support, C i * f i = 1 := by
    rw [Finset.sum_coe_sort C.support (fun i => C i * f i)]
    exact hC
  have hf : ∀ x, τ (f x) = f x := fun x => by
    simp only [f]
    rw [map_mul, hττ, mul_comm]
  choose g hg using fun x => hfix (f x) (hf x)
  have hs : ∀ x, τ (C x + τ (C x)) = C x + τ (C x) := fun x => by
    rw [map_add (f := _), hττ, add_comm]
  choose s hs' using fun x => hfix _ (hs x)
  have h2 : ∑ i : C.support, s i * g i = 2 := by
    apply ha
    have hc := congrArg τ hC'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one] at hc
    simp only [map_mul τ, hf] at hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_ofNat]
    simp only [map_mul, hg, hs', add_mul]
    rw [Finset.sum_add_distrib, hC', hc, one_add_one_eq_two]
  have h3 : ∑ i : C.support, (k * s i) * g i = 1 := by
    simp only [mul_assoc]
    rw [← Finset.mul_sum, h2, hk]
  obtain ⟨e, t, he1, heo, het⟩ := hid C.support (fun i => g i) _ h3
  have ha1 : ∑ i, a (e i) = 1 := by rw [← map_sum, he1, map_one]
  refine ⟨∑ i : C.support, a (e i) • i.1.1.map ι, ?_, ?_⟩
  · ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
      map_mul, hτa, hτι]
    exact Finset.sum_congr rfl fun x _ => by rw [x.1.2]
  · have : c * (∑ i : C.support, a (e i) • i.1.1.map ι) + d =
        ∑ i : C.support, a (e i) • (c * i.1.1.map ι + d) := by
      simp only [smul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, ha1, one_smul, Finset.mul_sum]
      simp only [Matrix.mul_smul]
    rw [this]
    refine isUnit_glue _ (fun i => a (t i) * τ (u i)) _ ha1 (fun i j hij => ?_) (fun i => ?_)
    · rw [← map_mul, heo i j hij, map_zero]
    · rw [← het i, map_mul, hg, mul_assoc, mul_comm (τ (u i))]

end Generic

theorem cA_algebraMap {D : D7} (a : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  rw [Algebra.algebraMap_eq_smul_one, GlobalTheory.FinTranslate.cA_smul, map_one]

theorem algebraMap_inj {D : D7} : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
  Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective

theorem half_mul_two {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A] :
    algebraMap F A (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap F A) 2, ← map_mul]
  simp

theorem exists_herm_isUnit (D : D7) (n : ℕ) (c d p q : Mx D n n) (h : c * p + d * q = 1) :
    ∃ x : Mx D n n, GlobalTheory.MixModel.adj x = x ∧ IsUnit (c * x + d) :=
  exists_herm_isUnit_generic (D.sp.cm.sig : D.host.E →+* D.host.E) D.host.xi0 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
    (GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D) (incA D) (cA D) GlobalTheory.DualPairCheck.cA_incA GlobalTheory.DualPairCheck.cA_cA
    (algebraMap (AF D.host.F) (AE D)) algebraMap_inj cA_algebraMap
    (fun y hy => GlobalTheory.DetRootRows.exists_baseRing_of_conjugation_fixed_tensor D.sp.cm.sig
      (fun x => (D.sp.cm.fixed (x + star x)).1 (by rw [star_add, star_star, add_comm])) y hy)
    (algebraMap D.host.F (AF D.host.F) (1 / 2)) half_mul_two (GlobalTheory.T.exists_orthogonal_idempotents_of_sum_mul_eq_one' D.host.F) c d p q h

end GlobalTheory.HermTransversal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMemMultT
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.Core.Rk.TopLift

open GlobalTheory.Mem.ColAd Filter Topology

section Comp

variable {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n)

theorem finN_mem_UPts (g : GA D V) : finN V hn g ∈ Formalism.UG.UPts D.sp.cm.sig (V.gram.reindex (finCongr hn) (finCongr hn))
    (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  subst hn
  exact GlobalTheory.PrincInLevel.swap_mem_UPts _ _ _ (GlobalTheory.UnitarySplit.finHom_mem V g)

theorem finN_eq (g : GA D V) (y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (h : ∀ i j, (Formalism.UG.bc (Lev.swapAE D) (finHom V g)).1 i j = y.1 (finCongr hn i) (finCongr hn j)) : finN V hn g = y := by
  subst hn
  exact Units.ext (Matrix.ext h)

theorem infN_atTau (hθ : IsInfFam θ) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (ρ : D.what₂.Tau) :
    (infN θ V hn (Equiv.refl _) (atTau θ V τ g) ρ : Matrix (Fin n) (Fin n) ℂ) =
      (Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ g ρ).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  have h : IsAtTau θ V τ g (atTau θ V τ g) := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg
  show Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ ρ) (atTau θ V τ g) = Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ g ρ
  by_cases c : ρ = τ
  · subst c
    rw [Function.update_self]
    exact h.2.1
  · rw [Function.update_of_ne c]
    exact h.2.2 ρ c


end Comp

section Main

variable {D : D7} {u : D.what₂.Word} {K : ClsPTied u} (θ : InfFam D)

def finPt (h : GA D D.sp.X') : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  ⟨finN D.sp.X' (rankP D) h, finN_mem_UPts D.sp.X' (rankP D) h⟩

theorem finPt_mul (h k : GA D D.sp.X') : (finPt (h * k)).1 = (finPt h).1 * (finPt k).1 := map_mul (finN D.sp.X' (rankP D)) h k

abbrev infPt : GA D D.sp.X' →* (D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) := infN θ D.sp.X' (rankP D) (Equiv.refl _)

theorem finPt_of_hasMat {h : GA D D.sp.X'} {y} (hh : HasMat h y) : (finPt h).1 = y := finN_eq _ (rankP D) h y hh.2

variable {g : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → FrP D → ℂ}

theorem finPt_mul_inf (h : GA D D.sp.X') {k : GA D D.sp.X'} (hk : k ∈ GinfC D.sp.X') : finPt (h * k) = finPt h := by
  refine Subtype.ext ?_
  rw [finPt_mul, show (finPt k).1 = 1 from finN_of_inf (rankP D) hk, mul_one]

theorem infPt_of_fin {k : GA D D.sp.X'} (hk : k ∈ GfC D.sp.X') : infPt θ k = 1 := infN_of_fin θ (rankP D) _ hk

variable (Bf : (FrP D → ℂ) →ₗ⋆[ℂ] (FrP D → ℂ) →ₗ[ℂ] ℂ)

end Main

end GlobalTheory.Core.Rk.TopLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalDoubleCosetRepresentativeBoundsStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_double_coset_representative_bounds : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1 + 1)) k), IsGL ι (L.h j al P) g → (∃ r ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j)) (c + 1 + 1) 1, GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j (c + 1) (by omega) (r * g)) → ∀ h' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k, flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g h' ≠ 0 → ∃ γ : AutY X R (j + 1), (∃ g' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k, IsGL ι γ g' ∧ DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J g' = DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J h') ∧ (∀ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1, γ⁻¹ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1 ∧ ((qOf P.1 : X.E) ^ (j + 1)) • γ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1) ∧ FiniteSumNonzeroLargeDepth Ch sel mu cst j P (L.h j al P) γ := by
  first | exact @GlobalTheory.TwBridge.repsOnto | exact GlobalTheory.TwBridge.repsOnto | (intros; apply GlobalTheory.TwBridge.repsOnto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThetaFunctionSchrodingerFunctionEq
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

namespace GlobalTheory.SchwOnto

noncomputable def ser (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (φ : Mx D B.rank A.rank → ℂ) :
    WO (dblSp A) B → ℂ := fun w =>
  ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)

theorem schw_onto : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ φ : Mx D B.rank A.rank → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∃ f, IsThetaFunO ψ (dblSp A) B f ∧ sch ψ A B ν 𝓨 f = φ := by
  intro D ψ hψ A B ν 𝓨 hν φ hφ
  have hlaw := _root_.GlobalTheory.ThetaSeriesLaw.law_and_level D ψ hψ A B φ hφ (ser D ψ A B φ) (fun _ => rfl)
  have hcs := GlobalTheory.T.thetaSeries_schwartzBruhat_continuous_schrodinger D ψ hψ A B ν 𝓨 hν φ hφ (ser D ψ A B φ) (fun _ => rfl)
  let V : Set (WO (dblSp A) B → ℂ) := {g | ∃ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ g = ser D ψ A B φ'}
  have hVc : ∀ g ∈ V, Continuous g := by
    rintro g ⟨φ', hφ', rfl⟩
    exact (GlobalTheory.T.thetaSeries_schwartzBruhat_continuous_schrodinger D ψ hψ A B ν 𝓨 hν φ' hφ' (ser D ψ A B φ') (fun _ => rfl)).1
  have hVd : ∀ g ∈ V, ∀ M : ℝ →+ WO (dblSp A) B, Continuous M → (∀ t, (M t).map (finPart D) = 0) →
      ∃ g' ∈ V, ∀ w, HasDerivAt (fun t : ℝ => heisO ψ (dblSp A) B (M t) g w) (g' w) 0 := by
    rintro g ⟨φ', hφ', rfl⟩ M hM hMf
    obtain ⟨φ'', hφ'', hd⟩ := GlobalTheory.T.hasDerivAt_heisenberg_thetaSeries D ψ hψ A B φ' hφ' (ser D ψ A B φ') (fun _ => rfl) M hM hMf
    exact ⟨ser D ψ A B φ'', ⟨φ'', hφ'', rfl⟩, hd (ser D ψ A B φ'') (fun _ => rfl)⟩
  have hsm := _root_.GlobalTheory.HeisSmooth.contDiff_of_heis_closed D ψ hψ (dblSp A) B V hVc hVd (ser D ψ A B φ) ⟨φ, hφ, rfl⟩
  exact ⟨ser D ψ A B φ, { quasi := hlaw.1, level := hlaw.2, cont := hcs.1, smooth := hsm }, hcs.2⟩

end GlobalTheory.SchwOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamGen1
section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem famGen1 : CorankOneIsEquivalenceOnRow → FamGen1 := by
  intro hE D X Y u hT
  obtain ⟨hrefl0, hsym, htr⟩ := hE D X Y u u hT
  have hnz : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t ∈ (Y.tO u u).nzSet := fun t ht => ht.1
  have hG : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t.G ≠ 0 := by
    intro t ht h0
    have h1 : (Y.tO u u).G t ≠ 0 := ht.1
    apply h1
    show Gt t = 0
    simp [Gt, h0]
  have hrefl : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t ∈ cls1 Y u t :=
    fun t ht => ⟨ht, rfl, hrefl0 t (hnz t ht)⟩
  have hrow : ∀ t t' : TauC Y u u, t' ∈ cls1 Y u t → (Y.tO u u).rowOf t' = (Y.tO u u).rowOf t :=
    fun t t' h => h.2.1
  have hsub : ∀ t ∈ (Y.tO u u).genSet, ∀ t' ∈ (Y.tO u u).genSet,
      (Y.tO u u).rowOf t = (Y.tO u u).rowOf t' → (Y.tO u u).s0 t t' = 1 →
      cls1 Y u t' ⊆ cls1 Y u t := by
    intro t ht t' ht' hr hs x hx
    obtain ⟨hxg, hxr, hxs⟩ := hx
    exact ⟨hxg, hxr.trans hr.symm, htr t (hnz t ht) t' (hnz t' ht') x (hnz x hxg) hr hxr.symm hs hxs⟩
  refine ⟨?_, ?_, ?_⟩
  · ext t
    simp [setQ, Formalism.FourierDecayAlt.PB.Terms.genSet]
  · intro t ht t' ht' hn
    constructor
    · intro he
      have : t' ∈ cls1 Y u t := he ▸ hrefl t' ht'
      exact (hrow t t' this).symm
    · intro hr
      have hs := GlobalTheory.Core.OneCoset.corankOne_of_same_flagDoubleCoset D X Y u u t t' (hG t ht) hr hn
      have hs' := hsym t (hnz t ht) t' (hnz t' ht') hr hs
      exact Set.Subset.antisymm (hsub t' ht' t ht hr.symm hs') (hsub t ht t' ht' hr hs)
  · intro t ht t' ht' he
    have : t' ∈ cls1 Y u t := he ▸ hrefl t' ht'
    exact (hrow t t' this).symm

end GlobalTheory.Core.One
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodPositionSplitLinesReadCompletionsAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPosition_splitLines_read_completions_at_place : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀) (x : Pl D), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) ∧ IsSelfDualC (c.V j) (N j) ∧ latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) → (∀ j ρ h, IsSelfDualC _ (o.M j ρ h) ∧ IsSelfDualC _ (M j ρ h) ∧ latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) → (GoodAt v o x → GoodAt { v with N := N } { o with M := M } x) ∧ (SplitAt v o x → SplitAt { v with N := N } { o with M := M } x) := by
  first | exact @GlobalTheory.LocCongr.goodAt_splitAt_congr | exact GlobalTheory.LocCongr.goodAt_splitAt_congr | (intros; apply GlobalTheory.LocCongr.goodAt_splitAt_congr <;> assumption)
end

