module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactEntriesBd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnePowNotMemHeightOneAsIdeal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1348
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def OpenBdd {a : Type} [Fintype a] [DecidableEq a] (H : Subgroup (GL a k)) : Prop :=
  IsOpen (H : Set (GL a k)) ∧ ∃ C : Set (GL a k), IsCompact C ∧ (H : Set (GL a k)) ⊆ C

theorem openBdd_of_le {a : Type} [Fintype a] [DecidableEq a] {H : Subgroup (GL a k)} (h1 : KOne k a ≤ H) (h2 : H ≤ KO k a) :
    OpenBdd H :=
  ⟨Subgroup.isOpen_mono h1 isOpen_KOne, _, isCompact_KO, h2⟩

theorem OpenBdd.map {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {H : Subgroup (GL a k)}
    (hH : OpenBdd H) (f : GL a k ≃* GL b k) (hf : Continuous f) (hf' : Continuous f.symm) : OpenBdd (H.map f.toMonoidHom) := by
  have e : ((H.map f.toMonoidHom : Subgroup (GL b k)) : Set (GL b k)) = f.symm ⁻¹' (H : Set (GL a k)) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_map, Set.mem_preimage, MulEquiv.coe_toMonoidHom]
    exact ⟨fun ⟨y, hy, e⟩ => by rw [← e, MulEquiv.symm_apply_apply]; exact hy,
      fun h => ⟨_, h, MulEquiv.apply_symm_apply _ _⟩⟩
  obtain ⟨ho, C, hC, hHC⟩ := hH
  refine ⟨e ▸ ho.preimage hf', f '' C, hC.image hf, ?_⟩
  rw [e]
  intro x hx
  exact ⟨_, hHC hx, MulEquiv.apply_symm_apply _ _⟩

theorem continuous_reGL {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) :
    Continuous (reGL (k := k) e) :=
  Continuous.units_map _ (continuous_id.matrix_reindex _ _)

theorem continuous_reGL_symm {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) :
    Continuous (reGL (k := k) e).symm := by
  have : (reGL (k := k) e).symm = reGL e.symm := by
    ext g i j
    rfl
  rw [this]
  exact continuous_reGL e.symm

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem openBdd_givenLevel (t : T) (w : Pl D.host.E) (i : ℕ) : OpenBdd (givenLevel G t w (i, D.R.m)) := by
  obtain ⟨m', hm⟩ : ∃ m', D.R.m = m' + 1 := ⟨D.R.m - 1, by have := D.R.two_le_m; omega⟩
  have key : ∀ X : ℕ × ℕ, X = (i, m' + 1) → OpenBdd (givenLevel G t w X) := by
    rintro _ rfl
    rcases i with _ | i
    · refine OpenBdd.map ?_ _ (continuous_reGL _) (continuous_reGL_symm _)
      unfold stepGroup
      split_ifs
      · exact openBdd_of_le (TypeDatum.KOne_le _) (TypeDatum.le_KO _)
      · exact openBdd_of_le (TypeDatum.KOne_le _) (TypeDatum.le_KO _)
      · exact openBdd_of_le KOne_le_KO le_rfl
    · exact openBdd_of_le KOne_le_KO le_rfl
  exact key _ (by rw [hm])

theorem openBdd_conjLevel (t : T) (w : Pl D.host.E) (g : (locGrid G t w).VertexGroup) {j : ℕ} (h0 : 0 < j)
    (hj : j < (locGrid G t w).m) : OpenBdd (conjLevel (G := locGrid G t w) one_le_sLen (givenLevel G t w) g hj) := by
  have hK : OpenBdd (givenLevel G t w ((locGrid G t w).m, j)) := by
    obtain ⟨m', hm⟩ : ∃ m', (locGrid G t w).m = m' + 1 := ⟨(locGrid G t w).m - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have key : ∀ X : ℕ × ℕ, X = (m' + 1, j' + 1) → OpenBdd (givenLevel G t w X) := by
      rintro _ rfl
      exact openBdd_of_le KOne_le_KO le_rfl
    exact key _ (by rw [hm])
  refine OpenBdd.map (OpenBdd.map hK _ ?_ ?_) _ ?_ ?_
  · exact (continuous_const.mul continuous_id).mul continuous_const
  · exact (continuous_const.mul continuous_id).mul continuous_const
  · exact Continuous.units_map _ (continuous_id.matrix_reindex _ _)
  · exact Continuous.units_map _ (continuous_id.matrix_reindex _ _)

theorem isCO_prodLev (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) {n' : P → ℕ}
    (h : ∀ w, n' w = V.rank) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (hK : ∀ w, OpenBdd (K w)) :
    IsCO V (prodLev β P h K) :=
  have ho := ProdOpen.isOpen_comap_prodLev V β P h K fun w => (hK w).1
  ⟨ho, GlobalTheory.ProdLevCompactC.isCompact_levA V β P h K (fun w => (hK w).2) ho⟩

variable (W : G.Weil) {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum)

theorem openBdd_pr (β : CosFam G t) (w : locPl G t) (j : ℕ) (h0 : 0 < j) (hj : j < D.R.m) :
    OpenBdd ((S.term t Φ β w).pr j h0 hj) := by
  obtain ⟨ho, hb⟩ := openBdd_conjLevel t w.1 ((repsAt G t w).elt (β w)) h0 hj
  exact SymImageC.symPr_open_bounded _ ho hb

namespace GridChoice

theorem isCO_levTop (β : CosFam G t) {j : ℕ} (hj : j < D.R.m) : IsCO (G.V (.top j)) (S.levTop t Φ β j hj) := by
  rcases j with _ | j
  · exact congLev_open_compact _ (GlobalTheory.AdIsom.selfDual_isFullLattice (isV_Xp G).sd) (G.pl.modul_ne_bot sc)
  · exact isCO_prodLev _ _ _ _ _ fun w => openBdd_pr W S t Φ β w (j + 1) j.succ_pos hj

theorem isCO_levRow {i : ℕ} (hi : i ≤ D.R.m) : IsCO (G.V (.grid i D.R.m)) (S.levRow t i hi) :=
  isCO_prodLev _ _ _ _ _ fun w => openBdd_givenLevel t w.1 i

end GridChoice


variable (G) in
theorem posDef_top {j : ℕ} (hj : j ≤ D.R.m) (φ : D.host.E →+* ℂ) : ((G.V (.top j)).gram.map φ).PosDef := by
  have h := G.isV (X := .top j) hj (fun _ e => by cases e)
  have := h.sigOK φ
  rw [h.sig φ] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem posDef_grid {μ₀ : T} (hL : L.Is μ₀) {i : ℕ} (hi : i ≤ D.R.m) (φ : D.host.E →+* ℂ) :
    ((G.V (.grid i D.R.m)).gram.map φ).PosDef := by
  have h := node_isV G hL (X := .grid i D.R.m) ⟨hi, le_rfl⟩
  have := h.sigOK φ
  rw [h.sig φ] at this
  simp only [Node.neg, Nat.sub_self, Nat.zero_div, Nat.sub_zero] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem readOK {n : ℕ} (σ : D.what₂.Tau → DomWeight n) : ReadOK σ := by
  obtain ⟨φ, h, -⟩ := funForm (K := ℂ) σ
  exact readOK_of_equiv σ φ fun F => (h F _).2 rfl

namespace GridChoice

theorem sumOK_classes {μ₀ : T} (hL : L.Is μ₀) :
    (∀ β, Finite (S.Classes t Φ β)) ∧ (∀ β (c : S.Classes t Φ β), S.invGam c ≠ 0) ∧
    (∀ i, i < D.R.m → WtOK G (.top t i) ∧ WtOK G (.chi i D.R.m)) ∧
    (∀ τ, Formalism.L2.Col.Br.Interlace G.sp.topDec.rank.symm (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ) ∧
      Formalism.L2.Col.Br.SameShift (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ)) ∧
    (ReadOK (listedWt G (.grid 0 D.R.m)) ∧ ReadOK (listedWt G (.grid D.R.m D.R.m))) := by
  have hT : ∀ β (j : Fin D.R.m), Finite (FinCl _ (S.levTop t Φ β j j.2)) ∧ ∀ x, gamOrd _ (S.levTop t Φ β j j.2) x ≠ 0 :=
    fun β j => ClassFin.finite_finCl_and_gamOrd _ _ (posDef_top G j.2.le) (isCO_levTop W S t Φ β j.2)
  have hR : ∀ i : Fin (D.R.m + 1), Finite (FinCl _ (S.levRow t i (Nat.le_of_lt_succ i.2))) ∧
      ∀ x, gamOrd _ (S.levRow t i (Nat.le_of_lt_succ i.2)) x ≠ 0 :=
    fun i => ClassFin.finite_finCl_and_gamOrd _ _ (posDef_grid hL (Nat.le_of_lt_succ i.2)) (isCO_levRow W S t (Nat.le_of_lt_succ i.2))
  refine ⟨fun β => ?_, fun β c => ?_, fun i hi => ⟨wtOK_of_defPair G (.top t i) hi, wtOK_of_defPair G (.chi i D.R.m) ⟨hi, rfl⟩⟩,
    GlobalTheory.WtInterlaceC.weights_top_grid G, readOK _, readOK _⟩
  · have := fun j => (hT β j).1
    have := fun i => (hR i).1
    exact inferInstance
  · unfold GridChoice.invGam
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => inv_ne_zero (Nat.cast_ne_zero.2 ((hT β j).2 _)))
      (Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (Nat.cast_ne_zero.2 ((hR i).2 _)))

end GridChoice

end GlobalTheory.FunObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsAndSymplecticIntegralOnPlaceLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.AdelicU GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.LatticeAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def Gd (v : HeightOneSpectrum (𝓞 F)) (x : AF F) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) x ∧ evFin F v x ∈ v.adicCompletionIntegers F

theorem gd_zero (v : HeightOneSpectrum (𝓞 F)) : Gd v (0 : AF F) :=
  ⟨fun u _ => smul_zero u, by rw [map_zero]; exact zero_mem _⟩

theorem gd_add {v : HeightOneSpectrum (𝓞 F)} {x y : AF F} (hx : Gd v x) (hy : Gd v y) : Gd v (x + y) :=
  ⟨fun u hu => by rw [smul_add, hx.1 u hu, hy.1 u hu, add_zero], by rw [map_add]; exact add_mem hx.2 hy.2⟩

theorem gd_neg {v : HeightOneSpectrum (𝓞 F)} {x : AF F} (hx : Gd v x) : Gd v (-x) :=
  ⟨fun u hu => by rw [smul_neg, hx.1 u hu, neg_zero], by rw [map_neg]; exact neg_mem hx.2⟩

theorem gd_mul {v : HeightOneSpectrum (𝓞 F)} {x y : AF F} (hx : Gd v x)
    (hy : evFin F v y ∈ v.adicCompletionIntegers F) : Gd v (x * y) :=
  ⟨fun u hu => by rw [← smul_mul_assoc, hx.1 u hu, zero_mul], by rw [map_mul]; exact mul_mem hx.2 hy⟩

theorem ev_alg (v : HeightOneSpectrum (𝓞 F)) (y : F) :
    evFin F v (algebraMap F (AF F) y) = algebraMap F (Fv F v) y := AlgHom.commutes _ y

def bil (σ : E →ₐ[F] E) {n d : ℕ} (ξ : E) (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin d) (Fin d) E) :
    LinearMap.BilinForm (AF F) (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
  LinearMap.mk₂ (AF F) (symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY))
    (fun x x' y => by
      simp only [symp, hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add (f := _)])
    (fun a x y => by
      simp only [symp, hTens, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm, map_smul])
    (fun x y y' => by
      simp only [symp, hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add (f := _)])
    (fun a x y => by
      simp only [symp, hTens, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm, map_smul])

theorem symp_incM (σ : E →ₐ[F] E) {n d : ℕ} (ξ : E) (JX : Matrix (Fin n) (Fin n) E)
    (JY : Matrix (Fin d) (Fin d) E) (x y : Matrix (Fin n) (Fin d) E) :
    symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F y) = algebraMap F (AF F) (symp σ ξ JX JY x y) := by
  have ht : ∀ e : E, Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (inclR (F := F) (AF F) e) =
      algebraMap F (AF F) (Algebra.trace F E e) := fun e => by
    show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  have hc : ∀ e : E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  rw [symp, symp, ← ht]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hTens, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hc, map_mul, map_sum]

end GlobalTheory.LatticeAtPlace

namespace GlobalTheory.LatticeAtPlace

theorem coords_symp_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin d) (Fin d) E) (ξ : E) (v : HeightOneSpectrum (𝓞 F))
    (co : (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))
    (T₀ : Set (Matrix (Fin n) (Fin d) E)) (yf zf : Matrix (Fin n) (Fin d) E → Fin n × Fin d → F),
    (∀ x, co (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (yf x k), fun k => algebraMap F (AF F) (zf x k))) →
    (∀ t ∈ T₀, ∀ k, algebraMap F (Fv F v) (yf t k) ∈ v.adicCompletionIntegers F ∧
      algebraMap F (Fv F v) (zf t k) ∈ v.adicCompletionIntegers F) →
    (∀ t ∈ T₀, ∀ t' ∈ T₀, algebraMap F (Fv F v) (GlobalTheory.WeilM.symp σ ξ JX JY t t') ∈ v.adicCompletionIntegers F) →
    ∀ γ ∈ AddSubgroup.closure {z | ∃ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
        ∃ t ∈ T₀, z = a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t},
      (∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co γ).1 k) ∧ evFin F v ((co γ).1 k) ∈ v.adicCompletionIntegers F ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co γ).2 k) ∧ evFin F v ((co γ).2 k) ∈ v.adicCompletionIntegers F) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ)
                   (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY) γ γ) ∧
        evFin F v (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY) γ γ) ∈ v.adicCompletionIntegers F) := by
  intro F E _ _ _ _ _ σ n d JX JY ξ v co T₀ yf zf hco hyz hs γ hγ
  set S : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := {z | ∃ a : AF F,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
      ∃ t ∈ T₀, z = a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t} with hS
  have hcoord : ∀ z ∈ AddSubgroup.closure S, ∀ k, Gd v ((co z).1 k) ∧ Gd v ((co z).2 k) := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha1, ha2, t, ht, rfl⟩ := hz
      intro k
      rw [map_smul, hco]
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      exact ⟨gd_mul ⟨ha1, ha2⟩ (by rw [ev_alg]; exact (hyz t ht k).1),
        gd_mul ⟨ha1, ha2⟩ (by rw [ev_alg]; exact (hyz t ht k).2)⟩
    | zero =>
      intro k
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
      exact ⟨gd_zero v, gd_zero v⟩
    | add x y _ _ hx hy =>
      intro k
      simp only [map_add (f := _), Prod.fst_add, Prod.snd_add, Pi.add_apply]
      exact ⟨gd_add (hx k).1 (hy k).1, gd_add (hx k).2 (hy k).2⟩
    | neg x _ hx =>
      intro k
      simp only [map_neg, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply]
      exact ⟨gd_neg (hx k).1, gd_neg (hx k).2⟩
  have hgen : ∀ x ∈ S, ∀ y ∈ S, Gd v (bil σ ξ JX JY x y) := by
    rintro _ ⟨a, ha1, ha2, t, ht, rfl⟩ _ ⟨b, -, hb2, t', ht', rfl⟩
    rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    have e : bil σ ξ JX JY (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t') =
        algebraMap F (AF F) (symp σ ξ JX JY t t') := symp_incM σ ξ JX JY t t'
    rw [e]
    refine gd_mul ⟨ha1, ha2⟩ ?_
    rw [map_mul, ev_alg]
    exact mul_mem hb2 (hs t ht t' ht')
  have hpair : ∀ x ∈ AddSubgroup.closure S, ∀ y ∈ AddSubgroup.closure S, Gd v (bil σ ξ JX JY x y) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy => exact hgen x hx y hy
      | zero => rw [map_zero]; exact gd_zero v
      | add y y' _ _ h h' => rw [map_add (f := _)]; exact gd_add h h'
      | neg y _ h => rw [map_neg]; exact gd_neg h
    | zero => intro y _; rw [map_zero, LinearMap.zero_apply]; exact gd_zero v
    | add x x' _ _ h h' => intro y hy; rw [map_add (f := _), LinearMap.add_apply]; exact gd_add (h y hy) (h' y hy)
    | neg x _ h => intro y hy; rw [map_neg, LinearMap.neg_apply]; exact gd_neg (h y hy)
  have hp := hpair γ hγ γ hγ
  exact ⟨fun k => ⟨(hcoord γ hγ k).1.1, (hcoord γ hγ k).1.2, (hcoord γ hγ k).2.1, (hcoord γ hγ k).2.2⟩, hp.1, hp.2⟩

end GlobalTheory.LatticeAtPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverSkewHermitianAdelicMatricesShrunkCompact
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SkewAdCover

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_sigR (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, sig_sig σ h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR (AF F) σ (inclR (F := F) (AF F) e) = inclR (AF F) (σ e) := by
  simp [sigR, inclR]

theorem sigR_alg (σ : E →ₐ[F] E) (c : F) :
    sigR (AF F) σ (algebraMap F (AF F ⊗[F] E) c) = algebraMap F (AF F ⊗[F] E) c :=
  (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ).commutes c

theorem inclR_alg (c : F) : inclR (F := F) (AF F) (algebraMap F E c) = algebraMap F (AF F ⊗[F] E) c :=
  (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).commutes c

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _

theorem cT_apply {A : Type} [CommRing A] (s : A →+* A) {m p : Type} (M : Matrix m p A) (i : p) (k : m) :
    cT s M i k = s (M k i) := rfl

theorem cover (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (j : ℕ) : ∃ (Ω : Set (AF F ⊗[F] E)) (B : ℝ), IsCompact Ω ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ (j * μ i) ∧ (∀ y ∈ Y, cT (sigR (AF F) σ) y = -y) ∧ ∀ x : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) x = -x → ∃ x₀ : Matrix (Fin j) (Fin j) E, cT (σ : E →+* E) x₀ = -x₀ ∧ ∃ y ∈ Y, ∃ ω : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) ω = -ω ∧ (∀ i k, ω i k ∈ Ω) ∧ x = adMat F x₀ + (y + (tor F E fun i => (μ i : ℤ)).1 * ω * cT (sigR (AF F) σ) (tor F E fun i => (μ i : ℤ)).1) := by
  classical
  haveI := hσ.1
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨Ω₀, C₀, hΩ₀, hcov⟩ := _root_.GlobalTheory.Eis.ConvCover.exists_cover F
  obtain ⟨Ω, C, hΩ, h⟩ := GlobalTheory.T.skewHermitian_adelic_cover_of_adele_cover F E σ hσ _ _ _ hΩ₀ hcov j
  set s := sigR (AF F) σ with hs_def
  set hh : AF F ⊗[F] E := algebraMap F (AF F ⊗[F] E) 2⁻¹ with hh_def
  have h2 : hh * 2 = 1 := by
    rw [hh_def, ← map_ofNat (algebraMap F (AF F ⊗[F] E)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hsh : s hh = hh := sigR_alg σ _
  have hss : ∀ z, s (s z) = z := sigR_sigR σ hσ
  have hsi : ∀ e, s (inclR (F := F) (AF F) e) = inclR (AF F) (σ e) := sigR_inclR σ
  let sk : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin j) (Fin j) (AF F ⊗[F] E) :=
    fun z => Matrix.of fun i k => hh * (z i k - s (z k i))
  have sk_skew : ∀ z, cT s (sk z) = -sk z := fun z => by
    ext i k
    simp only [cT_apply, sk, Matrix.of_apply, Matrix.neg_apply, map_mul, map_sub, hsh, hss]
    ring
  have hcont : Continuous fun p : (AF F ⊗[F] E) × (AF F ⊗[F] E) => hh * (p.1 - s p.2) :=
    continuous_const.mul (continuous_fst.sub ((continuous_sigR σ).comp continuous_snd))
  refine ⟨_, C, (hΩ.prod hΩ).image hcont, fun μ => ?_⟩
  obtain ⟨Y, hY, hc⟩ := h μ
  have hd : ∀ i, s ((GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i) = (GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i := fun i => by
    rw [map_pow, hs_def, GlobalTheory.Eis.Conv.sigR_halfE]
  have htor : (tor F E fun i => (μ i : ℤ)).1 = Matrix.diagonal fun i => (GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i := by
    simp [tor, GlobalTheory.Eis.Conv.dg]
  have htor' : cT s (tor F E fun i => (μ i : ℤ)).1 = Matrix.diagonal fun i => (GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i := by
    rw [htor]
    ext i k
    rw [cT_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hik : i = k
    · subst hik; simp [hd]
    · simp [hik, Ne.symm hik]
  refine ⟨Y.image sk, (Nat.cast_le.mpr Finset.card_image_le).trans (hY.trans (le_of_eq ?_)), ?_, fun x hx => ?_⟩
  · simp only [bse, ← pow_mul, mul_comm _ 2, show (4 : ℝ) = 2 ^ 2 by norm_num]
  · intro y hy
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hy
    exact sk_skew z
  · obtain ⟨S₀, y, hy, ω, hω, e⟩ := hc x hx
    set c : E := algebraMap F E 2⁻¹ with hc_def
    have hσc : σ c = c := σ.commutes _
    refine ⟨Matrix.of fun i k => c * (S₀ i k - σ (S₀ k i)), ?_, sk y, Finset.mem_image_of_mem _ hy, sk ω, sk_skew ω,
      fun i k => ⟨(ω i k, ω k i), ⟨hω i k, hω k i⟩, rfl⟩, ?_⟩
    · ext i k
      simp only [cT_apply, Matrix.of_apply, Matrix.neg_apply, AlgHom.coe_toRingHom, map_mul, map_sub, hσc,
        sig_sig σ hσ]
      ring
    · rw [htor', htor]
      ext i k
      have hx1 : s (x k i) = - x i k := by
        have := congrFun (congrFun hx i) k
        rwa [cT_apply, Matrix.neg_apply] at this
      have e1 := congrFun (congrFun e i) k
      have e2 := congrArg s (congrFun (congrFun e k) i)
      simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, map_add (f := _), map_mul,
        hsi, hd] at e1 e2
      rw [hx1] at e2
      simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, adMat, Matrix.map_apply,
        Matrix.of_apply, sk, map_mul, map_sub, inclR_alg]
      rw [hc_def, inclR_alg, ← hh_def]
      linear_combination hh * e1 - hh * e2 - x i k * h2
end GlobalTheory.SkewAdCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRapidDecaySiegelGLOfFinite
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspRapidDecaySiegelGL_of_finite (hfin : GlobalTheory.Published.AutomorphicFormsFiniteGL) :
    GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ ω hω hωB _ t ht lam
  obtain ⟨Ω, Kf, hΩ, hKf, hgeom⟩ := GlobalTheory.T.siegelSet_adelicGL_exists_compact_decomposition E a ω hω hωB t ht
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_translates_smoothFunction_of_compact E a φ hφ.1.level Kf hKf
  have hcore := fun f' : GL (Fin a) (Af E) =>
    _root_.GlobalTheory.cuspForm_rapidDecay_siegel hfin E a (finRep E a f' φ) (GlobalTheory.T.isCuspForm_operator_act hfin E a (.fin f') φ hφ) Ω hΩ t ht lam
  choose C hC0 hC using hcore
  refine ⟨∑ f' ∈ S, C f', fun b hb r hr hchain hprod k hk => ?_⟩
  obtain ⟨d, hd, hdiag⟩ := GlobalTheory.T.exists_realDiagonal_infGL_eq_positiveIdeleDiagonal E a r hr
  rw [hdiag]
  obtain ⟨c, hc, f, hf, heq⟩ := hgeom r d hr hchain hd b hb k hk
  rw [heq]
  obtain ⟨f', hf', hff'⟩ := hS f hf
  have e : φ.1 (infGL E a (d * c) * finGL E a f) = (finRep E a f' φ).1 (infGL E a (d * c)) := by
    rw [← hff']; rfl
  rw [e]
  refine (hC f' r d hr hchain hd hprod c hc).trans ?_
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hC0 i) hf')
    (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hr i).le _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueModificationLiftSqZeroFlagStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_modification_lift_sqZero_flag : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) {K : Type} [Field K] {ι : Type} (z : Sp K ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ M.off → ∀ (w : Sp (TrivSqZeroExt K (ι → K)) ⟶ X.YY), spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom ≫ w = z ≫ toFlag M → ∃ w' : Sp (TrivSqZeroExt K (ι → K)) ⟶ M.X, w' ≫ toFlag M = w ∧ spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom ≫ w' = z ∧ ∀ O : M.X.Opens, ⊤ ≤ z ⁻¹ᵁ O → ⊤ ≤ w' ⁻¹ᵁ O := by
  first | exact @GlobalTheory.ModifLift.exists_lift_sqZero | exact GlobalTheory.ModifLift.exists_lift_sqZero | (intros; apply GlobalTheory.ModifLift.exists_lift_sqZero <;> assumption)
end

