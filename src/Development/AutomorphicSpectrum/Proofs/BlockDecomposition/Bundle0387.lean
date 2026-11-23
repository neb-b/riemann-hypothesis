module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.SquareIntegrableAtPlace.SqIntAt

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstTermEqZeroOfFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ConstTermConj

open GlobalTheory.Cusp GlobalTheory.AutomorphicL2Unitary GlobalTheory.MixModel

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] {Γ N₁ N₂ : Subgroup G}
  [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ]
  [LocallyCompactSpace N₁] [LocallyCompactSpace N₂]

theorem constTermOn_eq_of_conj {φ : G → ℂ} (hφ : LeftInv Γ φ) {γ : G} (hγ : γ ∈ Γ)
    (hN : ∀ n, n ∈ N₁ ↔ γ * n * γ⁻¹ ∈ N₂) (x : G) :
    constTermOn Γ N₂ φ x = constTermOn Γ N₁ φ (γ⁻¹ * x) := by
  let e : N₁ ≃ₜ* N₂ :=
    { toFun := fun n => ⟨γ * n * γ⁻¹, (hN _).1 n.2⟩
      invFun := fun n => ⟨γ⁻¹ * n * γ, (hN _).2 (by simp [mul_assoc])⟩
      left_inv := fun n => by simp [mul_assoc]
      right_inv := fun n => by simp [mul_assoc]
      map_mul' := fun a b => by simp [mul_assoc]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let m := e.toHomeomorph.toMeasurableEquiv
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N₂) (Measure.haar.map e)
  have hp : MeasurePreserving m Measure.haar (Measure.haar.map e) := ⟨m.measurable, rfl⟩
  have h' : IsFundamentalDomain (Γ.subgroupOf N₁) (m ⁻¹' stdDom (Γ.subgroupOf N₂)) Measure.haar :=
    h.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun δ => ⟨e.symm δ, mul_mem (mul_mem (inv_mem hγ) δ.2) hγ⟩)
      ⟨fun a b hab => Subtype.ext (e.symm.injective (congrArg Subtype.val hab)),
        fun δ => ⟨⟨e δ, mul_mem (mul_mem hγ δ.2) (inv_mem hγ)⟩, Subtype.ext (e.symm_apply_apply _)⟩⟩
      fun δ n => (map_mul e _ _).trans (congrArg (· * e n) (e.apply_symm_apply _))
  rw [constTermOn_eq h hφ, constTermOn_eq h' hφ, ← hp.setIntegral_preimage_emb m.measurableEmbedding,
    measureReal_def, measureReal_def, hp.measure_preimage h.nullMeasurableSet]
  refine congrArg _ (integral_congr_ae (.of_forall fun n => ?_))
  change φ (γ * n * γ⁻¹ * x) = φ (n * (γ⁻¹ * x))
  rw [mul_assoc, mul_assoc, hφ γ hγ]

end Abstract

variable {D : D7} {V : HSp D} {r : ℕ}

theorem rat_mulVec_inc {n m : ℕ} (A : Matrix (Fin n) (Fin m) D.host.E) (x : Fin m → D.host.E) :
    (rat A).mulVec (fun i => incA D (x i)) = fun i => incA D ((A.mulVec x) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, rat, map_sum]

theorem conj_conditions {C₁ C₂ : Matrix (Fin V.rank) (Fin r) D.host.E}
    (g₀ gi : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (h1 : g₀ * gi = 1)
    (hC : g₀ * C₁ = C₂) (hC' : gi * C₂ = C₁) (hH : C₂ᴴ * V.gram * g₀ = C₁ᴴ * V.gram)
    (m : Mx D V.rank V.rank) (a1 : m * rat C₁ = 0) (a2 : rat (C₁ᴴ * V.gram) * m = 0)
    (a3 : ∀ x : Fin V.rank → D.host.E, (C₁ᴴ * V.gram).mulVec x = 0 →
      ∃ a : Fin r → AE D, m.mulVec (fun i => incA D (x i)) = (rat C₁).mulVec a) :
    (rat g₀ * m * rat gi) * rat C₂ = 0 ∧ rat (C₂ᴴ * V.gram) * (rat g₀ * m * rat gi) = 0 ∧
      ∀ x : Fin V.rank → D.host.E, (C₂ᴴ * V.gram).mulVec x = 0 →
        ∃ a : Fin r → AE D, (rat g₀ * m * rat gi).mulVec (fun i => incA D (x i)) = (rat C₂).mulVec a := by
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [Matrix.mul_assoc, ← rat_mul, hC', Matrix.mul_assoc, a1, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← rat_mul, hH, a2, Matrix.zero_mul]
  · have hy : (C₁ᴴ * V.gram).mulVec (gi.mulVec x) = 0 := by
      rw [← hH, Matrix.mulVec_mulVec, Matrix.mul_assoc (C₂ᴴ * V.gram) g₀ gi, h1, Matrix.mul_one, hx]
    obtain ⟨a, ha⟩ := a3 _ hy
    refine ⟨a, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rat_mulVec_inc, ha, Matrix.mulVec_mulVec, ← rat_mul, hC]

theorem conj_mem_NI {C₁ C₂ : Matrix (Fin V.rank) (Fin r) D.host.E} (γ : GA D V)
    (g₀ gi : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (h1 : g₀ * gi = 1) (h2 : gi * g₀ = 1)
    (hu : g₀ᴴ * V.gram * g₀ = V.gram) (hm : mt V γ = rat g₀) (hmi : mt V γ⁻¹ = rat gi)
    (hC : g₀ * C₁ = C₂) {n : GA D V} (hn : n ∈ NI V C₁) : γ * n * γ⁻¹ ∈ NI V C₂ := by
  have hC' : gi * C₂ = C₁ := by rw [← hC, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hH : C₂ᴴ * V.gram * g₀ = C₁ᴴ * V.gram := by
    rw [← hC, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g₀ᴴ, hu]
  have ii' : rat g₀ * rat gi = (1 : Mx D V.rank V.rank) := by rw [← rat_mul, h1, rat_one]
  have hle : NI V C₁ ≤ (NI V C₂).comap (MulAut.conj γ).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun g hg => Subgroup.subset_closure ?_
    obtain ⟨a1, a2, a3⟩ := hg
    have em : (matHom V ((MulAut.conj γ).toMonoidHom g)).1 - 1 = rat g₀ * ((matHom V g).1 - 1) * rat gi := by
      have e : (matHom V ((MulAut.conj γ).toMonoidHom g)).1 = mt V γ * mt V g * mt V γ⁻¹ := rfl
      rw [e, hm, hmi, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ii']
      rfl
    have := conj_conditions g₀ gi h1 hC hC' hH _ a1 a2 a3
    rw [← em] at this
    exact this
  exact hle hn

theorem rank_eq_of_isIsoFrame {C : Matrix (Fin V.rank) (Fin r) D.host.E} (h : IsIsoFrame V C) : C.rank = r := by
  have := LinearIndependent.rank_matrix (M := Cᵀ) h.2.1
  simpa [Matrix.rank_transpose] using this

theorem constTerm_eq_zero_of_frame : ∀ (D : D7) (V : HSp D) (r : ℕ) (C₁ C₂ : Matrix (Fin V.rank) (Fin r) D.host.E)
    (h₁ : IsIsoFrame V C₁) (h₂ : IsIsoFrame V C₂) (φ : GA D V → ℂ), (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) →
    GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h₁) φ = 0 → GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h₂) φ = 0 := by
  intro D V r C₁ C₂ h₁ h₂ φ hφ h0
  have hθ : (1 / 2 : D.host.E) + star (1 / 2 : D.host.E) = 1 := by
    have e : star (1 / 2 : D.host.E) = 1 / 2 := by simp
    rw [e, add_halves]
  have e₁ : C₁ᴴ * V.gram * C₁ = 0 := h₁.2.2
  have e₂ : C₂ᴴ * V.gram * C₂ = 0 := h₂.2.2
  obtain ⟨g₀, hu, hC⟩ := GlobalTheory.WittTrace.exists_isometry_mul_eq D.host.E (1 / 2) hθ V.rank r V.gram C₁ C₂
    (gram_conjTranspose V) (gram_isUnit_det V) (rank_eq_of_isIsoFrame h₁) (rank_eq_of_isIsoFrame h₂) (e₁.trans e₂.symm)
  obtain ⟨gi, hgi⟩ : ∃ gi, gi = V.gram⁻¹ * (g₀ᴴ * V.gram) := ⟨_, rfl⟩
  have h2 : gi * g₀ = 1 := by
    rw [hgi, Matrix.mul_assoc, hu, Matrix.nonsing_inv_mul _ (gram_isUnit_det V)]
  have h1 : g₀ * gi = 1 := mul_eq_one_comm.1 h2
  have hC' : gi * C₂ = C₁ := by rw [← hC, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hu' : giᴴ * V.gram * gi = V.gram := by
    calc giᴴ * V.gram * gi = giᴴ * (g₀ᴴ * V.gram * g₀) * gi := by rw [hu]
      _ = (g₀ * gi)ᴴ * V.gram * (g₀ * gi) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = V.gram := by rw [h1]; simp
  have hh : adj (rat g₀) * (gA V * rat g₀) = gA V := by
    rw [← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, ← Matrix.mul_assoc, hu]
  obtain ⟨γ, hm⟩ : ∃ γ : GA D V, mt V γ = rat g₀ := ⟨ofMat V (rat g₀) hh, mt_ofMat V _ hh⟩
  have hmi : mt V γ⁻¹ = rat gi := by
    have e := mt_mul_inv V γ
    rw [hm] at e
    calc mt V γ⁻¹ = (rat gi * rat g₀) * mt V γ⁻¹ := by rw [← rat_mul, h2, rat_one, Matrix.one_mul]
      _ = rat gi := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
  have hγ : γ ∈ GQ V := (mem_GQ_iff V γ).2 (hm ▸ rat_mem g₀)
  have hN : ∀ n, n ∈ NA (frameFlag h₁) ↔ γ * n * γ⁻¹ ∈ NA (frameFlag h₂) := fun n => by
    rw [NA_frameFlag, NA_frameFlag]
    refine ⟨conj_mem_NI γ g₀ gi h1 h2 hu hm hmi hC, fun h => ?_⟩
    have := conj_mem_NI γ⁻¹ gi g₀ h2 h1 hu' hmi (by simpa using hm) hC' h
    simpa [mul_assoc] using this
  funext x
  exact (constTermOn_eq_of_conj hφ hγ hN x).trans (congrFun h0 _)

end GlobalTheory.CompanionTheory.ConstTermConj

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CreqAnnqTopqSame
section
open Finset
open scoped InnerProductSpace
open GlobalTheory.CompanionTheory.PairMult
open Formalism.REAL (GlRel KHighest)
open CompanionTheory.D.LK (Pos)
open CompanionTheory.RgExh.U (adC)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

noncomputable section

namespace GlobalTheory.CompanionTheory.PairMult.TopK

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem sgL_erase (l : Lt n) (B : Finset (Lt n)) : sgL l (B.erase l) = sgL l B := by
  unfold sgL
  congr 2
  ext j
  simp only [mem_filter, mem_erase]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · exact fun h => ⟨⟨fun e => by subst e; exact lt_irrefl _ h.2, h.1⟩, h.2⟩

theorem sgL_sq (l : Lt n) (B : Finset (Lt n)) : sgL l B * sgL l B = 1 := by
  unfold sgL; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem adC_diag_ne {p q : Fin n} (h : p ≠ q) (i : Pos n) : adC p q i i = 0 := by
  have h1 : ¬(q = i.1.1 ∧ i.1 = (p, i.1.2)) := fun e => h (by
    have := congrArg Prod.fst e.2
    exact (this.symm.trans e.1.symm))
  have h2 : ¬(i.1.2 = p ∧ i.1 = (i.1.1, q)) := fun e => h (by
    have := congrArg Prod.snd e.2
    exact e.1.symm.trans this)
  simp [adC, h1, h2]

theorem adC_diag_self (p : Fin n) (i : Pos n) :
    adC p p i i = (if i.1.1 = p then 1 else 0) - (if i.1.2 = p then 1 else 0) := by
  have e1 : (p = i.1.1 ∧ i.1 = (p, i.1.2)) ↔ i.1.1 = p :=
    ⟨fun h => h.1.symm, fun h => ⟨h.symm, Prod.ext h rfl⟩⟩
  have e2 : (i.1.2 = p ∧ i.1 = (i.1.1, p)) ↔ i.1.2 = p :=
    ⟨fun h => h.1, fun h => ⟨h, Prod.ext rfl h⟩⟩
  simp only [adC, e1, e2]

theorem sum_diag {lev : Fin n → ℕ} (hm : Monotone lev) (p : Fin n) :
    (∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC p p i i else 0) = ((2 * rhoU lev p : ℝ) : ℂ) := by
  have hs : ∀ i : Pos n, (if lev i.1.1 < lev i.1.2 then adC p p i i else 0) =
      (if lev i.1.1 < lev i.1.2 ∧ i.1.1 = p then (1 : ℂ) else 0) -
        (if lev i.1.1 < lev i.1.2 ∧ i.1.2 = p then (1 : ℂ) else 0) := by
    intro i
    rw [adC_diag_self]
    by_cases h : lev i.1.1 < lev i.1.2 <;> simp [h]
  have c1 : (univ.filter fun i : Pos n => lev i.1.1 < lev i.1.2 ∧ i.1.1 = p).card =
      (univ.filter fun b => lev p < lev b).card := by
    refine Finset.card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · intro i hi
      obtain ⟨h1, h2⟩ := (mem_filter.1 hi).2
      exact mem_filter.2 ⟨mem_univ _, h2 ▸ h1⟩
    · intro i hi j hj e
      have h1 := (mem_filter.1 hi).2.2
      have h2 := (mem_filter.1 hj).2.2
      exact Subtype.ext (Prod.ext (h1.trans h2.symm) e)
    · intro b hb
      have hb' := (mem_filter.1 hb).2
      exact ⟨⟨(p, b), hm.reflect_lt hb'⟩, mem_filter.2 ⟨mem_univ _, hb', rfl⟩, rfl⟩
  have c2 : (univ.filter fun i : Pos n => lev i.1.1 < lev i.1.2 ∧ i.1.2 = p).card =
      (univ.filter fun b => lev b < lev p).card := by
    refine Finset.card_bij (fun i _ => i.1.1) ?_ ?_ ?_
    · intro i hi
      obtain ⟨h1, h2⟩ := (mem_filter.1 hi).2
      exact mem_filter.2 ⟨mem_univ _, h2 ▸ h1⟩
    · intro i hi j hj e
      have h1 := (mem_filter.1 hi).2.2
      have h2 := (mem_filter.1 hj).2.2
      exact Subtype.ext (Prod.ext e (h1.trans h2.symm))
    · intro b hb
      have hb' := (mem_filter.1 hb).2
      exact ⟨⟨(b, p), hm.reflect_lt hb'⟩, mem_filter.2 ⟨mem_univ _, hb', rfl⟩, rfl⟩
  rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, c1, c2]
  simp only [rhoU]
  push_cast
  ring

end GlobalTheory.CompanionTheory.PairMult.TopK

namespace GlobalTheory.CompanionTheory.PairMult.TopK

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem rhoU_eq {lev : Fin n → ℕ} {a b : Fin n} (h : lev a = lev b) : rhoU lev a = rhoU lev b := by
  simp only [rhoU, h]

theorem kF_bracket {E1 E2 : Fin n → Fin n → Module.End ℂ V} (g1 : GlRel E1) (g2 : GlRel E2)
    (hc : ∀ a b c d, E1 a b * E2 c d = E2 c d * E1 a b) (p q : Fin n) :
    kF E1 E2 q p * kF E1 E2 p q - kF E1 E2 p q * kF E1 E2 q p = kF E1 E2 q q - kF E1 E2 p p := by
  have h1 := g1 q p p q
  have h2 := g2 q p p q
  simp only [if_true] at h1 h2
  have e : kF E1 E2 q p * kF E1 E2 p q - kF E1 E2 p q * kF E1 E2 q p =
      (E1 q p * E1 p q - E1 p q * E1 q p) + (E2 q p * E2 p q - E2 p q * E2 q p) := by
    simp only [kF, add_mul, mul_add, hc q p p q, hc p q q p]
    abel
  rw [e, h1, h2]
  simp only [kF]
  abel

theorem K_act {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hl : IsLev lam lev) {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (hA : AdmFor lam lev E1 E2) {x : V} (hx : x ∈ hwSp E1 E2 (muQ lam lev)) {p q : Fin n} (hpq : lev p = lev q) :
    kF E1 E2 p q x = if p = q then ((muQ lam lev p : ℝ) : ℂ) • x else 0 := by
  have hK : KHighest (fun _ => true) (kF E1 E2) (muQ lam lev) x := hx
  rcases lt_trichotomy p q with h | rfl | h
  · rw [if_neg h.ne, hK.2 p q h rfl]
  · rw [if_pos rfl, hK.1 p]
  · rw [if_neg h.ne']
    have hmu : muQ lam lev q = muQ lam lev p := by
      simp only [muQ, rhoU_eq hpq.symm, hl.2 q p hpq.symm]
    have hb := LinearMap.congr_fun (kF_bracket hA.gl1 hA.gl2 hA.comm p q) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hK.2 q p h rfl, map_zero, sub_zero, hK.1 q, hK.1 p, hmu,
      sub_self] at hb
    have hn : ⟪kF E1 E2 p q x, kF E1 E2 p q x⟫_ℂ = 0 := by
      rw [hA.unitK p q x, hb, inner_zero_right]
    exact inner_self_eq_zero.1 hn

end GlobalTheory.CompanionTheory.PairMult.TopK
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalAlgebraHolds
section
open PositivityTheory.Rg.BcB.F.Eig

namespace GlobalTheory.CompanionTheory.BlockScalars

theorem diagOp_apply {ι : Type} {d : ℕ} (blk : Fin d → ι) (c : ι → ℂ)
    (x : EuclideanSpace ℂ (Fin d)) (j : Fin d) :
    (diagOp blk c x) j = c (blk j) * x j := by
  simp [diagOp, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

theorem diagAlg : DiagAlg := by
  intro ι d blk c c' z
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x j
    simp [diagOp_apply, ContinuousLinearMap.mul_def, mul_assoc]
  · ext x j
    simp [diagOp_apply, add_mul]
  · ext x j
    simp [diagOp_apply]
  · rw [ContinuousLinearMap.star_eq_adjoint]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    simp only [PiLp.inner_apply, diagOp_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [RCLike.inner_apply]
    ring

end GlobalTheory.CompanionTheory.BlockScalars
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNegStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_class_twist_neg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s) := by
  first | exact @GlobalTheory.CompanionTheory.ZcDual.dualCl_nu | exact GlobalTheory.CompanionTheory.ZcDual.dualCl_nu | (intros; apply GlobalTheory.CompanionTheory.ZcDual.dualCl_nu <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualOperatorCommutesLie
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.DualComm

variable {n : ℕ}

theorem sum_single_smul {W : Type*} [AddCommGroup W] [Module ℂ W] (Δ : Fin n → Fin n → W) (a b : Fin n) (c : ℂ) :
    ∑ x, ∑ y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • Δ x y = c • Δ a b := by
  have hx : ∀ x y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • Δ x y =
      if y = b then (if x = a then c • Δ a b else 0) else 0 := by
    intro x y
    by_cases h1 : x = a
    · by_cases h2 : y = b
      · subst h1
        subst h2
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, h1, h2, Ne.symm h2]
    · simp [Matrix.single_apply, h1, Ne.symm h1]
  simp only [hx, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem eq_zero_of_skew {W : Type*} [AddCommGroup W] [Module ℂ W] (Δ : Fin n → Fin n → W)
    (h : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → ∑ x, ∑ y, X x y • Δ x y = 0) (a b : Fin n) : Δ a b = 0 := by
  have h1 := h (Matrix.single a b 1 - Matrix.single b a 1) (by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_one,
      neg_sub])
  have h2 := h (Matrix.single a b Complex.I + Matrix.single b a Complex.I) (by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_single, Matrix.conjTranspose_single]
    ext i j
    simp [Matrix.single_apply]
    split_ifs <;> ring)
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_single_smul, one_smul] at h1 h2
  rw [sub_eq_zero] at h1
  rw [← h1, ← two_smul ℂ, smul_smul, smul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  · exact h2

theorem dualT_comp_rho (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (ξ : E.V →L[ℂ] ℂ) :
    dualT E T (ξ ∘L E.ρ k) = dualT E T ξ ∘L E.ρ k := by
  ext v
  have h := congrArg (fun f : E.V →L[ℂ] E.V => f v) (hT k)
  change T (E.ρ k v) = E.ρ k (T v) at h
  simp [dualT, h]

theorem dualT_sum (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T)
    (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) (hG : IsDualFam E G)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (ξ : E.V →L[ℂ] ℂ) :
    dualT E T (∑ a, ∑ b, X a b • G a b ξ) = ∑ a, ∑ b, X a b • G a b (dualT E T ξ) := by
  have hmem : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    intro t
    have hc : Commute ((t : ℂ) • X) (-((t : ℂ) • X)) := (Commute.refl _).neg_right
    have hs : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
      rw [Matrix.conjTranspose_smul, hX, smul_neg]
      simp
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hs,
      ← Matrix.exp_add_of_commute _ _ hc, add_neg_cancel, NormedSpace.exp_zero]
  let γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun t => ⟨NormedSpace.exp ((t : ℂ) • X), hmem t⟩
  have hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
  have h1 := hG.2 X γ hX hγ ξ
  have h2 := hG.2 X γ hX hγ (dualT E T ξ)
  have h3 : HasDerivAt (fun t : ℝ => dualT E T (ξ ∘L E.ρ (γ t)⁻¹))
      (dualT E T (∑ a, ∑ b, X a b • G a b ξ)) 0 :=
    ((dualT E T).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have hfun : (fun t : ℝ => dualT E T (ξ ∘L E.ρ (γ t)⁻¹)) =
      fun t : ℝ => dualT E T ξ ∘L E.ρ (γ t)⁻¹ := by
    funext t
    exact dualT_comp_rho E T hT (γ t)⁻¹ ξ
  rw [hfun] at h3
  exact h3.unique h2

theorem dualT_G : ∀ {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) →
    ∀ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G →
      ∀ a b ξ, dualT E T (G a b ξ) = G a b (dualT E T ξ) := by
  intro n E T hT G hG a b ξ
  have h := eq_zero_of_skew (fun a b => dualT E T (G a b ξ) - G a b (dualT E T ξ)) ?_ a b
  · exact sub_eq_zero.mp h
  · intro X hX
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero, ← dualT_sum E T hT G hG X hX ξ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]

end GlobalTheory.CompanionTheory.RealCountG.DualComm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpowRightEqPow
section
namespace GlobalTheory.CompanionTheory.PairMult

section Powers

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem epowLeft_eq_pow (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    PositivityTheory.RgBcC.RealD.epow E m a b =
      ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [PositivityTheory.RgBcC.RealD.epow, Matrix.one_apply]
  | succ m ih =>
    simp only [PositivityTheory.RgBcC.RealD.epow, pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem epowRight_eq_pow (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    Formalism.REAL.epow E m a b =
      ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [Formalism.REAL.epow, Matrix.one_apply]
  | succ m ih =>
    simp only [Formalism.REAL.epow, pow_succ, Matrix.mul_apply, Matrix.of_apply, ih]

theorem etr_eq_gelA (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) :
    Formalism.REAL.etr E m = PositivityTheory.RgBcC.RealD.gelA E m := by
  simp only [Formalism.REAL.etr, PositivityTheory.RgBcC.RealD.gelA, epowLeft_eq_pow, epowRight_eq_pow]

end Powers

end GlobalTheory.CompanionTheory.PairMult
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMeasurableIsFundamentalDomain
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.LatticeFD

theorem exists_measurable_isFundamentalDomain (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ)
    [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] :
    ∃ 𝓕 : Set (GA E N), MeasurableSet 𝓕 ∧ ∀ μ : Measure (GA E N), IsFundamentalDomain (latticeGL E N) 𝓕 μ :=
  ⟨GlobalTheory.AutomorphicL2Unitary.stdDom (latticeGL E N), GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom _,
    fun μ => GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ μ⟩

end GlobalTheory.CompanionTheory.LatticeFD

end
end

