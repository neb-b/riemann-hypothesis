module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import GroundTheory.Brauer.DoubleCentralizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0870
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0872
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoWEqZero
section
open NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LinWAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def coW (G : Geo σ a a') {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (u : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    Matrix (Fin a) (Fin (a + a')) (Fv F v) :=
  -(G.V.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ)

theorem coW_eq_zero (G : Geo σ a a') {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (u : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (h : u.map (piW (t.comp σ)) = 0) : coW G t u = 0 := by
  unfold coW; rw [h]; simp

end GlobalTheory.LinWAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionIntegralOfLimitStepsStatement
section
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnInclusionIntegral_of_limitSteps : LimActSt → LimPtSt → LimFrameSt → InclSt := by
  first | exact @GlobalTheory.IsoTriv.Incl.inclSt_of_lim | exact GlobalTheory.IsoTriv.Incl.inclSt_of_lim | (intros; apply GlobalTheory.IsoTriv.Incl.inclSt_of_lim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutantOfMaximalDegreeElement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CentIrr

noncomputable def rootHom (F C : Type) [Field F] [Ring C] [Algebra F C] (y : C) :
    AdjoinRoot (minpoly F y) →ₐ[F] C :=
  Ideal.Quotient.liftₐ (Ideal.span {minpoly F y}) (Polynomial.aeval y) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, minpoly.aeval, zero_mul])

theorem rootHom_root (F C : Type) [Field F] [Ring C] [Algebra F C] (y : C) :
    rootHom F C y (AdjoinRoot.root (minpoly F y)) = y := by
  exact Polynomial.aeval_X y

theorem commute_iff_mem_adjoin (F C : Type) [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C] (n : ℕ) (hn : 0 < n) (hC : Module.finrank F C = n ^ 2)
    (y : C) (hirr : Irreducible (minpoly F y)) (hdeg : (minpoly F y).natDegree = n) (z : C) :
    Commute z y ↔ z ∈ Algebra.adjoin F ({y} : Set C) := by
  set B := Algebra.adjoin F ({y} : Set C) with hBdef
  have hcommB : ∀ {u v : C}, u ∈ B → v ∈ B → u * v = v * u := by
    intro u v hu hv
    have := Algebra.adjoin_le_centralizer_centralizer F ({y} : Set C) hu
    rw [Subalgebra.mem_centralizer_iff] at this
    apply (this v _).symm
    refine Algebra.adjoin_le ?_ hv
    rw [Set.singleton_subset_iff, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
  haveI : Fact (Irreducible (minpoly F y)) := ⟨hirr⟩
  set j : AdjoinRoot (minpoly F y) →ₐ[F] C := rootHom F C y
  have hj : Function.Injective j := j.toRingHom.injective
  have hrange : j.range = B := by
    rw [← Algebra.map_top, ← AdjoinRoot.adjoinRoot_eq_top, AlgHom.map_adjoin, Set.image_singleton]
    rw [rootHom_root]
  have hne : minpoly F y ≠ 0 := hirr.ne_zero
  have hEdim : Module.finrank F (AdjoinRoot (minpoly F y)) = n := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  let eB : AdjoinRoot (minpoly F y) ≃ₐ[F] B := (AlgEquiv.ofInjective j hj).trans (Subalgebra.equivOfEq _ _ hrange)
  haveI : IsSimpleRing B := IsSimpleRing.of_ringEquiv eB.toRingEquiv inferInstance
  have hBdim : Module.finrank F B = n := by rw [← eB.toLinearEquiv.finrank_eq, hEdim]
  set Z := Subalgebra.centralizer F (B : Set C)
  have hBZ : B ≤ Z := by
    intro a ha
    rw [Subalgebra.mem_centralizer_iff]
    intro b hb
    exact hcommB hb ha
  have h1 := GroundTheory.Brauer.finrank_mul_finrank_centralizer (K := F) (A := C) B
  have hdim : Module.finrank F B = Module.finrank F Z := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < Module.finrank F B by rw [hBdim]; exact hn)
    rw [h1, hC, hBdim, sq]
  have hEq : B = Z := Subalgebra.toSubmodule_injective
    (Submodule.eq_of_le_of_finrank_eq (Subalgebra.toSubmodule.monotone hBZ) hdim)
  constructor
  · intro hz
    have hzZ : z ∈ Z := by
      rw [Subalgebra.mem_centralizer_iff]
      intro b hb
      have := Algebra.adjoin_le_centralizer_centralizer F ({y} : Set C) hb
      rw [Subalgebra.mem_centralizer_iff] at this
      refine (this z ?_).symm
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]; exact hz.eq.symm
    rw [hEq]; exact hzZ
  · intro hz
    exact (hcommB hz (Algebra.self_mem_adjoin_singleton F y) : _)

theorem centralizer_unit_eq_field : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (y₀ : G.Cˣ),
    Irreducible (minpoly G.F (y₀ : G.C)) → (minpoly G.F (y₀ : G.C)).natDegree = G.n →
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra G.F E) (j : E →ₐ[G.F] G.C),
      Function.Injective j ∧ ∀ z : G.C, Commute z (y₀ : G.C) ↔ ∃ e, j e = z := by
  intro p _ G y₀ hirr hdeg
  haveI : Fact (Irreducible (minpoly G.F (y₀ : G.C))) := ⟨hirr⟩
  let j : AdjoinRoot (minpoly G.F (y₀ : G.C)) →ₐ[G.F] G.C := rootHom G.F G.C (y₀ : G.C)
  have hne : minpoly G.F (y₀ : G.C) ≠ 0 := hirr.ne_zero
  haveI : FiniteDimensional G.F (AdjoinRoot (minpoly G.F (y₀ : G.C))) :=
    (AdjoinRoot.powerBasis hne).finite
  haveI : FiniteDimensional ℚ (AdjoinRoot (minpoly G.F (y₀ : G.C))) :=
    Module.Finite.trans G.F _
  haveI : CharZero (AdjoinRoot (minpoly G.F (y₀ : G.C))) :=
    charZero_of_injective_algebraMap (algebraMap G.F _).injective
  haveI : NumberField (AdjoinRoot (minpoly G.F (y₀ : G.C))) := ⟨⟩
  have hrange : j.range = Algebra.adjoin G.F ({(y₀ : G.C)} : Set G.C) := by
    rw [← Algebra.map_top, ← AdjoinRoot.adjoinRoot_eq_top, AlgHom.map_adjoin, Set.image_singleton]
    rw [rootHom_root]
  refine ⟨AdjoinRoot (minpoly G.F (y₀ : G.C)), inferInstance, inferInstance, inferInstance, j,
    j.toRingHom.injective, fun z => ?_⟩
  rw [commute_iff_mem_adjoin G.F G.C G.n G.n_pos G.rankC _ hirr hdeg z, ← hrange]
  rfl

end GlobalTheory.CentIrr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenLevelConjCommensurableStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactOpenLevel_conj_commensurable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (g : G.GAf), Subgroup.Commensurable (L.K.toSubgroup.map (MulAut.conj g).toMonoidHom) L.K.toSubgroup := by
  first | (exact @GlobalTheory.LKMid.level_conj_commensurable) | (exact GlobalTheory.LKMid.level_conj_commensurable) | (intros; apply GlobalTheory.LKMid.level_conj_commensurable  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUniformBound
section
namespace GlobalTheory.CompactUniformHeightBound

open Filter Topology

theorem height_one_le {E : Type} [Field E] [NumberField E] {a : ℕ}
    (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)) : 1 ≤ GlobalTheory.CuspRep.height y := by
  unfold GlobalTheory.CuspRep.height
  exact le_add_of_le_of_nonneg (le_add_of_nonneg_right (norm_nonneg _)) (norm_nonneg _)

theorem compact_uniform_bound : (let d1 : {E : Type} → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsTotallyComplex E] → {a : ℕ} → (GlobalTheory.CuspRep.GA E a → ℂ) → Prop := @(fun {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ} (F : GlobalTheory.CuspRep.GA E a → ℂ) ↦ ∀ (g₀ : GlobalTheory.CuspRep.GA E a), ∃ (C : ℝ) (N : ℕ), (0 : ℝ) ≤ C ∧ ∀ᶠ (g : GlobalTheory.CuspRep.GA E a) in nhds g₀, ∀ (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)), ‖F (g * (GlobalTheory.CuspRep.infGL E a : GL (Fin a) (GlobalTheory.CuspRep.Cinf E) → GlobalTheory.CuspRep.GA E a) y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N); ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsTotallyComplex E] {a : ℕ} {F : GlobalTheory.CuspRep.GA E a → ℂ}, d1 F → ∀ {K : Set (GlobalTheory.CuspRep.GA E a)}, IsCompact K → ∃ (C : ℝ) (N : ℕ), (0 : ℝ) ≤ C ∧ ∀ g ∈ K, ∀ (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)), ‖F (g * (GlobalTheory.CuspRep.infGL E a : GL (Fin a) (GlobalTheory.CuspRep.Cinf E) → GlobalTheory.CuspRep.GA E a) y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N) := by
  intro d1 E _ _ _ a F hF K hK
  have hb : ∀ g₀ : GlobalTheory.CuspRep.GA E a, ∃ (C : ℝ) (N : ℕ), (0 : ℝ) ≤ C ∧
      {g : GlobalTheory.CuspRep.GA E a | ∀ (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)),
        ‖F (g * (GlobalTheory.CuspRep.infGL E a : GL (Fin a) (GlobalTheory.CuspRep.Cinf E) → GlobalTheory.CuspRep.GA E a) y)‖
          ≤ C * GlobalTheory.CuspRep.height y ^ N} ∈ 𝓝 g₀ := fun g₀ => hF g₀
  choose C N hC hU using hb
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover _ (fun x _ => hU x)
  refine ⟨∑ x ∈ t, C x, t.sup N, Finset.sum_nonneg (fun x _ => hC x), ?_⟩
  intro g hg y
  obtain ⟨x, hx, hgx⟩ := Set.mem_iUnion₂.mp (hKt hg)
  have h1 := height_one_le y
  calc _ ≤ C x * GlobalTheory.CuspRep.height y ^ N x := hgx y
    _ ≤ (∑ i ∈ t, C i) * GlobalTheory.CuspRep.height y ^ t.sup N :=
      mul_le_mul (Finset.single_le_sum (fun i _ => hC i) hx)
        (pow_le_pow_right₀ h1 (Finset.le_sup hx))
        (pow_nonneg (zero_le_one.trans h1) _) (Finset.sum_nonneg fun i _ => hC i)

end GlobalTheory.CompactUniformHeightBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjByCarryingUnitMemPositiveSimilitudeFormGroup
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem pair_conj_mem_grp : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (B y : G.Cˣ) (s : ℚ), 0 < s → 0 < ((P.c : ℚˣ) : ℚ) → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → ((y⁻¹ * P.γ * y, P.c) : G.Cˣ × ℚˣ) ∈ grp G B := by
  intro p _ G P B y s hs hc hβ
  refine ⟨?_, hc⟩
  change ((y⁻¹ * P.γ * y : G.Cˣ) : G.C) * B * sh G ((y⁻¹ * P.γ * y : G.Cˣ) : G.C) = algebraMap ℚ G.C (P.c : ℚ) * B
  have hmul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have e : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← hmul, Units.inv_mul]; simp [sh]
  have hs0 : s ≠ 0 := hs.ne'
  have hβ' : (P.β : G.C) = s • ((y : G.C) * B * sh G y) := by rw [hβ, Algebra.smul_def]
  have hY : (y : G.C) * B * sh G y = s⁻¹ • (P.β : G.C) := by
    rw [hβ', smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hsim : (P.γ : G.C) * P.β * sh G P.γ = (P.c : ℚ) • (P.β : G.C) := by
    rw [P.sim, Algebra.smul_def]
  rw [Units.val_mul, Units.val_mul, hmul, hmul, ← Algebra.smul_def]
  calc ((y⁻¹ : G.Cˣ) : G.C) * P.γ * y * B * (sh G y * (sh G P.γ * sh G ((y⁻¹ : G.Cˣ) : G.C)))
      = ((y⁻¹ : G.Cˣ) : G.C) * (P.γ * ((y : G.C) * B * sh G y) * sh G P.γ) * sh G ((y⁻¹ : G.Cˣ) : G.C) := by
        simp only [mul_assoc]
    _ = s⁻¹ • (((y⁻¹ : G.Cˣ) : G.C) * ((P.γ : G.C) * P.β * sh G P.γ) * sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
        rw [hY]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = (s⁻¹ * (P.c : ℚ)) • (((y⁻¹ : G.Cˣ) : G.C) * (P.β : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
        rw [hsim, mul_smul]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = (s⁻¹ * (P.c : ℚ) * s) • ((((y⁻¹ : G.Cˣ) : G.C) * y) * B * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C))) := by
        rw [hβ', mul_smul (s⁻¹ * (P.c : ℚ)) s]; simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = (P.c : ℚ) • (B : G.C) := by
        rw [Units.inv_mul, e, one_mul, mul_one, mul_comm (s⁻¹) _, mul_assoc, inv_mul_cancel₀ hs0, mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjFrameMemUH
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicScalar

theorem conjFrame_mem_UH : ∀ (p q n : ℕ), p + q = n → ∀ (Gm : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), (Aᴴ * Formalism.UG.Jpq p q * A : Matrix (Fin n) (Fin n) ℂ) = Gm → IsUnit Gm.det → ∀ b : UpqT p q, conjFrame Gm A (UpqT.mat b) ∈ Formalism.QuantumDeterminants.UH Gm := by
  intro p q n hn Gm A hA hG b
  have hJ : (Formalism.UG.Jpq p q)ᴴ = Formalism.UG.Jpq p q := by simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have h1 : Gm⁻¹ * Gm = 1 := Matrix.nonsing_inv_mul _ hG
  have hb : (UpqT.mat b)ᴴ * Formalism.UG.Jpq p q * UpqT.mat b = Formalism.UG.Jpq p q := b.2
  have hl : (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * A = 1 := by rw [Matrix.mul_assoc, hA, h1]
  have e : Fin n ≃ Fin p ⊕ Fin q := (finCongr hn.symm).trans finSumFinEquiv.symm
  have hr : A * (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hl
  have hc : A * conjFrame Gm A (UpqT.mat b) = UpqT.mat b * A := by
    have : A * conjFrame Gm A (UpqT.mat b) = A * (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * (UpqT.mat b * A) := by
      simp only [conjFrame, Matrix.mul_assoc]
    rw [this, hr, Matrix.one_mul]
  change (conjFrame Gm A (UpqT.mat b))ᴴ * Gm * conjFrame Gm A (UpqT.mat b) = Gm
  generalize conjFrame Gm A (UpqT.mat b) = C at hc
  calc Cᴴ * Gm * C = (A * C)ᴴ * Formalism.UG.Jpq p q * (A * C) := by
        rw [← hA]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Aᴴ * ((UpqT.mat b)ᴴ * Formalism.UG.Jpq p q * UpqT.mat b) * A := by
        rw [hc]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Gm := by rw [hb, hA]

end GlobalTheory.AdelicScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemBlockUpperUnipotentRadicalStatement
section
open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mem_blockUpperUnipotentRadical : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b),
  ∀ p ∈ GlobalTheory.OrbDesc.blockPar (K := K) e, ∀ n ∈ GlobalTheory.OrbDesc.blockUni e, p * n * p⁻¹ ∈ GlobalTheory.OrbDesc.blockUni e := by
  first | exact @GlobalTheory.OrbDesc.blockUni_conj_mem | exact GlobalTheory.OrbDesc.blockUni_conj_mem | (intros; apply GlobalTheory.OrbDesc.blockUni_conj_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairsSameSimilitude
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem grp_factor_eq_of_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (y y₀ : grp G β) (c : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    (y : G.Cˣ × ℚˣ).2 = (y₀ : G.Cˣ × ℚˣ).2 := by
  intro p _ G β y y₀ c hyc
  haveI : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C
  haveI : Nontrivial G.C := inferInstance
  set d : G.C → ℚ := fun a => LinearMap.det (LinearMap.mulLeft ℚ a) with hd
  have dmul : ∀ a b, d (a * b) = d a * d b := by
    intro a b; simp only [hd, LinearMap.mulLeft_mul, LinearMap.det_comp]
  have done : d 1 = 1 := by simp [hd, LinearMap.mulLeft_one]
  have dsc : ∀ s : ℚ, d (algebraMap ℚ G.C s) = s ^ Module.finrank ℚ G.C := by
    intro s
    have : LinearMap.mulLeft ℚ (algebraMap ℚ G.C s) = s • LinearMap.id := by
      ext x; simp [Algebra.smul_def]
    simp only [hd, this, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have dunit : ∀ u : G.Cˣ, d (u : G.C) * d ((u⁻¹ : G.Cˣ) : G.C) = 1 := by
    intro u; rw [← dmul, Units.mul_inv, done]
  have shmul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have shone : sh G 1 = 1 := by simp [sh]
  have dsh_conj : d (sh G (c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C))) =
      d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
    have e : d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * d (sh G (c : G.C)) = 1 := by
      rw [← dmul, ← shmul, Units.mul_inv, shone, done]
    rw [shmul, shmul, dmul, dmul]
    calc d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * (d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * d (sh G (c : G.C)))
        = d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) *
          (d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * d (sh G (c : G.C))) := by ring
      _ = _ := by rw [e, mul_one]
  have d_conj : d (c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C)) =
      d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := by
    rw [dmul, dmul]
    calc d (c : G.C) * d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * d ((c⁻¹ : G.Cˣ) : G.C)
        = d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * (d (c : G.C) * d ((c⁻¹ : G.Cˣ) : G.C)) := by ring
      _ = _ := by rw [dunit, mul_one]
  obtain ⟨hy, hs⟩ := y.2
  obtain ⟨hy₀, hs₀⟩ := y₀.2
  have ey := congrArg d hy
  have ey₀ := congrArg d hy₀
  rw [dmul, dmul, dmul, dsc] at ey ey₀
  rw [hyc, d_conj, dsh_conj, ey₀] at ey
  have hβ : d (β : G.C) ≠ 0 := by
    intro h; have := dunit β; rw [h, zero_mul] at this; exact zero_ne_one this
  have hN : Module.finrank ℚ G.C ≠ 0 := Module.finrank_pos.ne'
  have hpow : ((y : G.Cˣ × ℚˣ).2 : ℚ) ^ Module.finrank ℚ G.C = ((y₀ : G.Cˣ × ℚˣ).2 : ℚ) ^ Module.finrank ℚ G.C :=
    (mul_right_cancel₀ hβ ey).symm
  exact Units.ext ((pow_left_inj₀ hs.le hs₀.le hN).1 hpow)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistedUnitCommutes
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem unit_conj_form_props {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β Y c : G.Cˣ) (s : ℚ) (hβ : sh G β = β)
    (h0 : (Y : G.C) * β * sh G Y = algebraMap ℚ G.C s * β)
    (h1 : ((c : G.C) * Y * ((c⁻¹ : G.Cˣ) : G.C)) * β * sh G ((c : G.C) * Y * ((c⁻¹ : G.Cˣ) : G.C)) =
      algebraMap ℚ G.C s * β) :
    IsUnit (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) ∧
    Commute (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) (Y : G.C) ∧
    (β : G.C) * sh G (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
      ((β⁻¹ : G.Cˣ) : G.C) = ((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C) := by
  have shm : ∀ x z : G.C, sh G (x * z) = sh G z * sh G x := fun x z => by simp [sh]
  have shs : ∀ x : G.C, sh G (sh G x) = x := G.star_star
  have sh1 : sh G 1 = 1 := sh_one_eq G
  set u : G.C := ((c⁻¹ : G.Cˣ) : G.C) with hu
  set bi : G.C := ((β⁻¹ : G.Cˣ) : G.C) with hbi_def
  set S : G.C := algebraMap ℚ G.C s with hS
  have hA : ∀ r : G.C, u * ((c : G.C) * r) = r := fun r => by rw [← mul_assoc, hu, Units.inv_mul, one_mul]
  have hB : sh G (c : G.C) * sh G u = 1 := by rw [← shm, hu, Units.inv_mul, sh1]
  have hB' : ∀ r : G.C, sh G (c : G.C) * (sh G u * r) = r := fun r => by rw [← mul_assoc, hB, one_mul]
  have hC : ∀ r : G.C, (β : G.C) * (bi * r) = r := fun r => by rw [← mul_assoc, hbi_def, Units.mul_inv, one_mul]
  have hC' : ∀ r : G.C, bi * ((β : G.C) * r) = r := fun r => by rw [← mul_assoc, hbi_def, Units.inv_mul, one_mul]
  have hD : (β : G.C) * bi = 1 := by rw [hbi_def, Units.mul_inv]
  set shYi : G.C := sh G ((Y⁻¹ : G.Cˣ) : G.C) with hshYi
  have hE : ∀ r : G.C, sh G (Y : G.C) * (shYi * r) = r := fun r => by
    rw [← mul_assoc, hshYi, ← shm, Units.inv_mul, sh1, one_mul]
  have hE1 : sh G (Y : G.C) * shYi = 1 := by rw [hshYi, ← shm, Units.inv_mul, sh1]
  refine ⟨?_, ?_, ?_⟩
  · have hshu : IsUnit (sh G u) := ⟨⟨sh G u, sh G (c : G.C), by rw [← shm, hu, Units.mul_inv, sh1], hB⟩, rfl⟩
    exact (((Units.isUnit _).mul (Units.isUnit β)).mul hshu).mul (Units.isUnit _)
  · have h2 : (Y : G.C) * (u * β * sh G u) * sh G Y = S * (u * β * sh G u) := by
      calc (Y : G.C) * (u * β * sh G u) * sh G Y
          = u * (((c : G.C) * Y * u) * β * sh G ((c : G.C) * Y * u)) * sh G u := by
            simp only [shm, mul_assoc, hA, hB, hB', mul_one]
        _ = S * (u * β * sh G u) := by
            rw [h1, hS, ← mul_assoc, ← Algebra.commutes s u]; simp only [mul_assoc]
    have e1 : (Y : G.C) * (u * β * sh G u * bi) = S * ((u * β * sh G u) * (shYi * bi)) := by
      calc (Y : G.C) * (u * β * sh G u * bi) = ((Y : G.C) * (u * β * sh G u) * sh G Y) * (shYi * bi) := by
            simp only [mul_assoc, hE]
        _ = _ := by rw [h2, mul_assoc]
    have eY : (Y : G.C) = S * ((β : G.C) * (shYi * bi)) := by
      calc (Y : G.C) = ((Y : G.C) * β * sh G Y) * (shYi * bi) := by
            simp only [mul_assoc, hE, hD, mul_one]
        _ = _ := by rw [h0, mul_assoc]
    have e2 : (u * β * sh G u * bi) * (Y : G.C) = S * ((u * β * sh G u) * (shYi * bi)) := by
      rw [eY]
      calc u * β * sh G u * bi * (S * ((β : G.C) * (shYi * bi)))
          = (u * β * sh G u) * (bi * S * ((β : G.C) * (shYi * bi))) := by simp only [mul_assoc]
        _ = (u * β * sh G u) * (S * (bi * ((β : G.C) * (shYi * bi)))) := by
            rw [hS, ← Algebra.commutes s bi]; simp only [mul_assoc]
        _ = _ := by rw [hC', ← mul_assoc, ← mul_assoc, ← Algebra.commutes s, hS]; simp only [mul_assoc]
    exact e2.trans e1.symm
  · have hbi : sh G bi = bi := by
      have h3 : sh G (β : G.C) * sh G bi = 1 := by rw [← shm, hbi_def, Units.inv_mul, sh1]
      rw [hβ] at h3
      calc sh G bi = (bi * β) * sh G bi := by rw [hbi_def, Units.inv_mul, one_mul]
        _ = bi := by rw [mul_assoc, h3, mul_one]
    simp only [shm, shs, hβ, hbi, mul_assoc, hC]

theorem grp_conj_unit_props : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β → ∀ (y y₀ : grp G β) (c : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    (y : G.Cˣ × ℚˣ).2 = (y₀ : G.Cˣ × ℚˣ).2 →
    IsUnit (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ Commute (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧
    (β : G.C) * sh G (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * ((β⁻¹ : G.Cˣ) : G.C) = (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β hβ y y₀ c hy hs
  have h0 : (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C ((y₀ : G.Cˣ × ℚˣ).2 : ℚ) * β := y₀.2.1
  have h1 : (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C ((y : G.Cˣ × ℚˣ).2 : ℚ) * β := y.2.1
  rw [hy, hs] at h1
  exact unit_conj_form_props G β _ c _ hβ h0 h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharpolyCoeffMulLeftFiniteAdelesAwayP
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CharpolyCont

theorem continuous_eval₂_of {X R : Type*} [TopologicalSpace X] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {σ : Type*} (f : ℤ →+* R) (P : MvPolynomial σ ℤ) (x : X → σ → R)
    (hx : ∀ i, Continuous fun t => x t i) : Continuous fun t => MvPolynomial.eval₂ f (x t) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval₂_C]; exact continuous_const
  | add P Q hP hQ => simp only [MvPolynomial.eval₂_add]; exact hP.add hQ
  | mul_X P i hP => simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]; exact hP.mul (hx i)

theorem continuous_charpoly_coeff_mulLeft {R A : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A] [TopologicalSpace A] [IsModuleTopology R A]
    (k : ℕ) : Continuous fun a : A => (LinearMap.charpoly (LinearMap.mulLeft R a)).coeff k := by
  let b := Module.Free.chooseBasis R A
  have e : ∀ a : A, (LinearMap.charpoly (LinearMap.mulLeft R a)).coeff k =
      MvPolynomial.eval₂Hom (Int.castRingHom R)
        (fun ij : Module.Free.ChooseBasisIndex R A × Module.Free.ChooseBasisIndex R A =>
          LinearMap.toMatrix b b (LinearMap.mulLeft R a) ij.1 ij.2)
        ((Matrix.charpoly.univ ℤ (Module.Free.ChooseBasisIndex R A)).coeff k) := by
    intro a
    rw [Matrix.charpoly.univ_coeff_eval₂Hom, ← LinearMap.charpoly_toMatrix _ b]
    rfl
  simp_rw [e]
  refine continuous_eval₂_of _ _ _ fun ij => ?_
  have h : ∀ a : A, LinearMap.toMatrix b b (LinearMap.mulLeft R a) ij.1 ij.2 =
      (b.coord ij.1).comp (LinearMap.mulRight R (b ij.2)) a := by
    intro a
    simp [LinearMap.toMatrix_apply]
  simp_rw [h]
  exact IsModuleTopology.continuous_of_linearMap _

end GlobalTheory.CharpolyCont

open GlobalTheory.CharpolyCont in
theorem GlobalTheory.charpoly_coeff_continuous_GAf : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ), Continuous fun g : G.GAf =>
    (LinearMap.charpoly (LinearMap.mulLeft (AfP p) (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) :
      AfP p ⊗[ℚ] G.C))).coeff k := by
  intro p _ G k
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) _
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  exact (continuous_charpoly_coeff_mulLeft (R := AfP p) (A := AfP p ⊗[ℚ] G.C) k).comp
    (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val))
end
end

