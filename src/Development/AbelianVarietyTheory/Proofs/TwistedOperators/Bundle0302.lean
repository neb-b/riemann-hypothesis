module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStableComplementOfIrreducibleSpanIntertwin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

noncomputable section

namespace GlobalTheory.RealQuot.SemisimpleSpan

open GlobalTheory.RealQuot

theorem isStab_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M] {σ : ι → Module.End ℂ M}
    (W : κ → Submodule ℂ M) (h : ∀ k, IsStab σ (W k)) : IsStab σ (⨆ k, W k) := by
  intro i
  have hle : (⨆ k, W k) ≤ (⨆ k, W k).comap (σ i) :=
    iSup_le fun k x hx => Submodule.mem_iSup_of_mem k (h k i x hx)
  exact fun x hx => hle hx

theorem exists_stab_compl_of_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M] (σ : ι → Module.End ℂ M)
    (W : κ → Submodule ℂ M) (hW : ∀ k, IsStab σ (W k))
    (hs : ∀ k (V : Submodule ℂ M), IsStab σ V → V ≤ W k → V = ⊥ ∨ V = W k) (htop : ⨆ k, W k = ⊤) :
    ∀ N : Submodule ℂ M, IsStab σ N → ∃ N' : Submodule ℂ M, IsStab σ N' ∧ IsCompl N N' := by
  letI : Module (FreeAlgebra ℂ ι) M :=
    Module.compHom M (FreeAlgebra.lift ℂ σ : FreeAlgebra ℂ ι →ₐ[ℂ] Module.End ℂ M).toRingHom
  have smul_def : ∀ (a : FreeAlgebra ℂ ι) (x : M), a • x = FreeAlgebra.lift ℂ σ a x := fun _ _ => rfl
  haveI : IsScalarTower ℂ (FreeAlgebra ℂ ι) M := ⟨fun c a x => by
    rw [smul_def, smul_def, map_smul]
    rfl⟩
  have key : ∀ N : Submodule ℂ M, IsStab σ N →
      ∃ W' : Submodule (FreeAlgebra ℂ ι) M, W'.restrictScalars ℂ = N := by
    intro N hN
    have hst : ∀ a : FreeAlgebra ℂ ι, ∀ x ∈ N, FreeAlgebra.lift ℂ σ a x ∈ N := by
      intro a
      induction a using FreeAlgebra.induction with
      | grade0 r =>
        intro x hx
        rw [AlgHom.commutes, Module.algebraMap_end_apply]
        exact N.smul_mem r hx
      | grade1 i =>
        intro x hx
        rw [FreeAlgebra.lift_ι_apply]
        exact hN i x hx
      | mul a b ha hb =>
        intro x hx
        rw [map_mul, Module.End.mul_apply]
        exact ha _ (hb x hx)
      | add a b ha hb =>
        intro x hx
        rw [map_add (f := _), LinearMap.add_apply]
        exact N.add_mem (ha x hx) (hb x hx)
    refine ⟨{ carrier := N
              add_mem' := N.add_mem
              zero_mem' := N.zero_mem
              smul_mem' := fun a x hx => hst a x hx }, ?_⟩
    ext x
    rfl
  have stabR : ∀ W' : Submodule (FreeAlgebra ℂ ι) M, IsStab σ (W'.restrictScalars ℂ) := by
    intro W' i x hx
    have : σ i x = (FreeAlgebra.ι ℂ i) • x := by rw [smul_def, FreeAlgebra.lift_ι_apply]
    rw [this]
    exact W'.smul_mem _ hx
  have hss : IsSemisimpleModule (FreeAlgebra ℂ ι) M := by
    rw [← sSup_simples_eq_top_iff_isSemisimpleModule, ← Submodule.restrictScalars_eq_top_iff ℂ,
      eq_top_iff, ← htop]
    refine iSup_le fun k => ?_
    obtain ⟨Wk, hWk⟩ := key (W k) (hW k)
    rw [← hWk]
    refine Submodule.restrictScalars_mono ℂ ?_
    by_cases h0 : Wk = ⊥
    · rw [h0]
      exact bot_le
    · refine le_sSup (isSimpleModule_iff_isAtom.2 ⟨h0, fun V hV => ?_⟩)
      rcases hs k (V.restrictScalars ℂ) (stabR V) (hWk ▸ Submodule.restrictScalars_mono ℂ hV.le) with h | h
      · exact (Submodule.restrictScalars_eq_bot_iff ℂ _ _).1 h
      · exact absurd ((Submodule.restrictScalars_injective ℂ _ _) (h.trans hWk.symm)) hV.ne
  intro N hN
  obtain ⟨WN, hWN⟩ := key N hN
  obtain ⟨W', hc⟩ := exists_isCompl WN
  refine ⟨W'.restrictScalars ℂ, stabR W', ⟨?_, ?_⟩⟩
  · rw [disjoint_iff, ← hWN, ← Submodule.restrictScalars_inf, hc.inf_eq_bot]
    rfl
  · rw [codisjoint_iff, ← hWN, ← Submodule.restrictScalars_sup, hc.sup_eq_top]
    rfl

theorem exists_stab_compl : ∀ (ι J Fm Q Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pi] [Module ℂ Pi] (ρ : ι → Module.End ℂ Q)
  (C : Submodule ℂ Q) (σ : ι → Module.End ℂ Pi) (τ : J → Module.End ℂ Pi) (β : Fm → Q →ₗ[ℂ] Pi),
  GlobalTheory.RealQuot.HoweCond ρ C → (∀ f i, β f ∘ₗ ρ i = σ i ∘ₗ β f) → (∀ f, C ≤ LinearMap.ker (β f)) →
  (∀ j f, ∃ f', τ j ∘ₗ β f = β f') → (⨆ f, LinearMap.range (β f)) = ⊤ →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → GlobalTheory.RealQuot.IsStab τ N → N = ⊥ ∨ N = ⊤) →
  ∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N' := by
  intro ι J Fm Q Pi _ _ _ _ ρ C σ τ β hH hint hker hτ hspan hirr
  obtain ⟨⟨L, hL⟩, -⟩ := hH
  have hcomm : ∀ f i x, β f (ρ i x) = σ i (β f x) := fun f i x => by
    rw [← LinearMap.comp_apply (β f) (ρ i), hint f i, LinearMap.comp_apply]
  let K : Submodule ℂ Q := ⨅ f, LinearMap.ker (β f)
  have hKf : ∀ f, K ≤ LinearMap.ker (β f) := fun f => iInf_le _ f
  have hKs : IsStab ρ K := by
    intro i x hx
    refine Submodule.mem_iInf _ |>.2 fun f => ?_
    rw [LinearMap.mem_ker, hcomm, LinearMap.mem_ker.1 (hKf f hx), map_zero]
  have hCK : C ≤ K := le_iInf hker

  have hmapS : ∀ S : Submodule ℂ Q, IsStab ρ S → ∀ f, IsStab σ (S.map (β f)) := by
    rintro S hS f i _ ⟨x, hx, rfl⟩
    exact ⟨ρ i x, hS i x hx, hcomm f i x⟩
  have hNS : ∀ S : Submodule ℂ Q, IsStab ρ S → (⨆ f, S.map (β f)) = ⊥ ∨ (⨆ f, S.map (β f)) = ⊤ := by
    intro S hS
    refine hirr _ (isStab_iSup _ (hmapS S hS)) ?_
    intro j
    have hle : (⨆ f, S.map (β f)) ≤ (⨆ f, S.map (β f)).comap (τ j) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨f', hf'⟩ := hτ j f
      show τ j (β f x) ∈ ⨆ f, S.map (β f)
      rw [← LinearMap.comp_apply, hf']
      exact Submodule.mem_iSup_of_mem f' ⟨x, hx, rfl⟩
    exact fun x hx => hle hx

  obtain ⟨S, hSst, hStop, hsimp⟩ : ∃ S : Submodule ℂ Q, IsStab ρ S ∧ (⨆ f, S.map (β f)) = ⊤ ∧
      ∀ f (V : Submodule ℂ Pi), IsStab σ V → V ≤ S.map (β f) → V = ⊥ ∨ V = S.map (β f) := by
    by_cases hK : K = ⊤
    · refine ⟨⊤, fun i x _ => Submodule.mem_top, by simpa [Submodule.map_top] using hspan, fun f V _ hV => Or.inl ?_⟩
      have h0 : (⊤ : Submodule ℂ Q).map (β f) = ⊥ := by
        rw [Submodule.map_top, LinearMap.range_eq_bot]
        exact LinearMap.ker_eq_top.1 (top_le_iff.1 (hK ▸ hKf f))
      exact le_bot_iff.1 (h0 ▸ hV)
    · let T : Type := {S : Submodule ℂ Q // IsStab ρ S ∧ C ≤ S}
      have wf : WellFounded (fun x y : T => x.1 < y.1) := by
        refine ⟨fun x => ?_⟩
        by_contra hx
        obtain ⟨g, -, hg⟩ := not_acc_iff_exists_descending_chain.1 hx
        have anti : StrictAnti fun n => (g n).1 := strictAnti_nat_of_succ_lt hg
        have mono : StrictMono fun k : Fin (L + 1) => (g (L - k.1)).1 := by
          intro a b hab
          exact anti (by have := a.2; have := b.2; simp only [Fin.lt_def] at hab; omega)
        have := hL (L + 1) _ mono fun k => (g (L - k.1)).2
        omega
      obtain ⟨M, hMK0, hMmin⟩ := wf.has_min {x : T | K < x.1}
        ⟨⟨⊤, fun i x _ => Submodule.mem_top, le_top⟩, lt_top_iff_ne_top.2 hK⟩
      have hMK : K < M.1 := hMK0
      refine ⟨M.1, M.2.1, ?_, ?_⟩
      · rcases hNS M.1 M.2.1 with h | h
        · exfalso
          refine hMK.2 (le_iInf fun f => ?_)
          intro x hx
          have h1 : β f x ∈ M.1.map (β f) := Submodule.mem_map_of_mem hx
          rw [iSup_eq_bot.1 h f] at h1
          exact LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 h1)
        · exact h
      · intro f V hVs hV
        let U : Submodule ℂ Q := M.1 ⊓ V.comap (β f)
        have hUs : IsStab ρ U := by
          rintro i x ⟨hx1, hx2⟩
          refine ⟨M.2.1 i x hx1, ?_⟩
          show β f (ρ i x) ∈ V
          rw [hcomm]
          exact hVs i _ hx2
        have hKU : K ≤ U := fun x hx => ⟨hMK.le hx, by
          show β f x ∈ V
          rw [LinearMap.mem_ker.1 (hKf f hx)]
          exact V.zero_mem⟩
        by_cases hlt : K < U
        · right
          have hUM : U = M.1 := by
            by_contra hne
            exact hMmin ⟨U, hUs, hCK.trans hKU⟩ hlt (lt_of_le_of_ne inf_le_left hne)
          refine le_antisymm hV ?_
          rintro _ ⟨x, hx, rfl⟩
          have : x ∈ U := hUM ▸ hx
          exact this.2
        · left
          have hUK : U = K := (eq_of_le_of_not_lt hKU hlt).symm
          rw [eq_bot_iff]
          intro v hv
          obtain ⟨x, hx, rfl⟩ := hV hv
          have : x ∈ U := ⟨hx, hv⟩
          rw [hUK] at this
          exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 (hKf f this))
  exact exists_stab_compl_of_iSup σ (fun f => S.map (β f)) (hmapS S hSst) hsimp hStop

end GlobalTheory.RealQuot.SemisimpleSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivConjOfGramTransposeEqNeg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GrpConj

variable {D : D7}

theorem conj_mem {R : Type} [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (c : R →+* R) (hc : ∀ x, c (c x) = x) (e : m ≃ n) (A : Matrix m m R) (B : Matrix n n R)
    (hAB : Aᵀ = -(B.submatrix e e)) (M : Matrix m m R) (hM : (M.map c)ᵀ * A * M = A) :
    (((M.map c).submatrix e.symm e.symm).map c)ᵀ * B * (M.map c).submatrix e.symm e.symm = B := by
  have hcc : (M.map c).map c = M := Matrix.ext fun i j => hc _
  have hB : B = (-Aᵀ).submatrix e.symm e.symm := by
    rw [hAB, neg_neg]; ext i j; simp
  have h2 : Mᵀ * Aᵀ * M.map c = Aᵀ := by
    have := congrArg Matrix.transpose hM
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at this
  rw [← Matrix.submatrix_map, hcc, Matrix.transpose_submatrix]
  conv_rhs => rw [hB]
  rw [hB, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.mul_neg, Matrix.neg_mul, h2]

theorem symm_hyp {R : Type} [CommRing R] {m n : Type} (e : m ≃ n) (A : Matrix m m R) (B : Matrix n n R)
    (hAB : Aᵀ = -(B.submatrix e e)) : Bᵀ = -(A.submatrix e.symm e.symm) := by
  have hB : B = (-Aᵀ).submatrix e.symm e.symm := by
    rw [hAB, neg_neg]; ext i j; simp
  rw [hB]; ext i j; simp

def gmap {R : Type} [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (c : R →+* R) (e : m ≃ n) : GL m R →* GL n R :=
  (Units.map (Matrix.reindexAlgEquiv R R e).toRingEquiv.toRingHom.toMonoidHom).comp (GeneralLinearGroup.map c)

theorem incM_hyp {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) :
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM V.gram)ᵀ = -((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM W.gram).submatrix e e) := by
  ext i j
  have k := congrArg (fun X => incA D (X i j)) h
  simpa [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.transpose_apply] using k

end GlobalTheory.GrpConj

namespace GlobalTheory.GrpConj

variable {D : D7}

def fwd (V W : HSp D) (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) : GA D V →* GA D W where
  toFun g := show HR (AF D.host.F) D.sp.cm.sig W.gram from ⟨gmap (cA D) e (matHom V g), by
    show ((((mt V g).map (cA D)).submatrix e.symm e.symm).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM W.gram *
      ((mt V g).map (cA D)).submatrix e.symm e.symm = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM W.gram
    exact conj_mem (cA D) Formalism.L2.Theta.cA_cA e _ _ (incM_hyp e h) _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram V g)⟩
  map_one' := by
    apply Subtype.ext
    show gmap (cA D) e (matHom V 1) = 1
    rw [map_one, map_one]
  map_mul' a b := by
    apply Subtype.ext
    show gmap (cA D) e (matHom V (a * b)) = gmap (cA D) e (matHom V a) * gmap (cA D) e (matHom V b)
    rw [map_mul, map_mul]

def conjEquiv (V W : HSp D) (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) : GA D V ≃* GA D W where
  toFun := fwd V W e h
  invFun := fwd W V e.symm (symm_hyp e _ _ h)
  left_inv g := by
    apply Subtype.ext; apply Units.ext; ext i j
    show cA D (cA D (mt V g (e.symm (e i)) (e.symm (e j)))) = mt V g i j
    rw [Formalism.L2.Theta.cA_cA]; simp
  right_inv g := by
    apply Subtype.ext; apply Units.ext; ext i j
    show cA D (cA D (mt W g (e (e.symm i)) (e (e.symm j)))) = mt W g i j
    rw [Formalism.L2.Theta.cA_cA]; simp
  map_mul' := (fwd V W e h).map_mul

theorem mt_conjEquiv (V W : HSp D) (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) (g : GA D V) :
    mt W (conjEquiv V W e h g) = ((mt V g).map (cA D)).submatrix e.symm e.symm := rfl

theorem continuous_conjEquiv (V W : HSp D) (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) :
    Continuous (conjEquiv V W e h) := by
  have h1 : Continuous (matHom V) := continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact ((Units.continuous_val.comp h1).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)).matrix_submatrix _ _
  · exact ((Units.continuous_coe_inv.comp h1).matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)).matrix_submatrix _ _

theorem inclR_inj : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem rat_conjEquiv (V W : HSp D) (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) (γ : GA D V)
    (hγ : γ ∈ GQ V) : conjEquiv V W e h γ ∈ GQ W := by
  obtain ⟨y, -, ey⟩ := hγ
  have e' : mt V γ = (y : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) :=
    (congrArg Units.val ey).symm
  set Z := ((y : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (D.sp.cm.sig : D.host.E →+* D.host.E)).submatrix
    e.symm e.symm with hZdef
  have hZ : mt W (conjEquiv V W e h γ) = Z.map (inclR (F := D.host.F) (AF D.host.F)) := by
    rw [mt_conjEquiv, e']; ext i j; rfl
  refine ⟨gmap (D.sp.cm.sig : D.host.E →+* D.host.E) e y, ?_, Units.ext ?_⟩
  · have hm := (conjEquiv V W e h γ).2
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt W (conjEquiv V W e h γ)) *
      JR (AF D.host.F) W.gram * mt W (conjEquiv V W e h γ) = JR (AF D.host.F) W.gram at hm
    rw [hZ] at hm
    have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (Z.map (inclR (F := D.host.F) (AF D.host.F))) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z).map (inclR (F := D.host.F) (AF D.host.F)) := by
      ext i j; rfl
    rw [hcT] at hm
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z * W.gram * Z = W.gram
    apply Matrix.map_injective inclR_inj
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul]
    exact hm
  · exact hZ.symm

theorem suppAt_conjEquiv (V W : HSp D) (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) (a : AE D)
    (g : GA D V) (hs : SuppAt a V g) : SuppAt a W (conjEquiv V W e h g) := by
  intro i j
  have k : (mt W (conjEquiv V W e h g) - 1) i j = cA D ((mt V g - 1) (e.symm i) (e.symm j)) := by
    rw [mt_conjEquiv]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.submatrix_apply, Matrix.map_apply, map_sub,
      EmbeddingLike.apply_eq_iff_eq]
    split_ifs <;> simp
  rw [k]
  have := congrArg (cA D) (hs (e.symm i) (e.symm j))
  rw [map_mul, map_add (f := _), Formalism.L2.Theta.cA_cA, add_comm] at this
  exact this

theorem det_conjEquiv (V W : HSp D) (e : Fin V.rank ≃ Fin W.rank) (h : V.gramᵀ = -(W.gram.submatrix e e)) (g : GA D V) :
    (mt W (conjEquiv V W e h g)).det = (mt V g⁻¹).det := by
  rw [mt_conjEquiv, Matrix.det_submatrix_equiv_self, GlobalTheory.ConjAdjWeil.det_inv_eq]
  exact (RingHom.map_det (cA D) _).symm

theorem exists_conj_equiv : ∀ (D : D7) (S T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank), T'.gramᵀ = -(S.gram.submatrix e₁ e₁) →
    ∃ φ' : GA D T' ≃* GA D S, Continuous φ' ∧ (∀ γ ∈ GQ T', φ' γ ∈ GQ S) ∧
      (∀ h, (Formalism.L2.Theta.mt S (φ' h)).submatrix e₁ e₁ = (Formalism.L2.Theta.mt T' h).map (cA D)) ∧
      (∀ e h, SuppAt e T' h → SuppAt e S (φ' h)) ∧ ∀ h, (Formalism.L2.Theta.mt S (φ' h)).det = (Formalism.L2.Theta.mt T' h⁻¹).det := by
  intro D S T' e₁ h
  refine ⟨conjEquiv T' S e₁ h, continuous_conjEquiv T' S e₁ h, rat_conjEquiv T' S e₁ h, fun g => ?_,
    fun a g hs => suppAt_conjEquiv T' S e₁ h a g hs, det_conjEquiv T' S e₁ h⟩
  rw [mt_conjEquiv]; ext i j; simp

end GlobalTheory.GrpConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinFLin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

noncomputable section

namespace GlobalTheory.FinFockLin

theorem finF_lin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X),
  IsFinF ψ θ ε A B 0 ∧ (∀ f g, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g → IsFinF ψ θ ε A B (f + g)) ∧
  (∀ (c : ℂ) f, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B (c • f)) ∧
  (∀ f g P, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g →
    fockF ψ θ ε A B (f + g) P = fockF ψ θ ε A B f P + fockF ψ θ ε A B g P) ∧
  ∀ (c : ℂ) f P, IsFinF ψ θ ε A B f → fockF ψ θ ε A B (c • f) P = c • fockF ψ θ ε A B f P := by
  intro D ψ θ hψ hθ ε M X A B
  have hsm : ∀ (c : ℂ) f, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B (c • f) := by
    intro c f hf
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c hf.1, fun τ z => ?_⟩
    rw [GlobalTheory.FockIndep.annih_smul hψ hθ τ _ z c hf.1, hf.2 τ z, smul_zero]
  have hadd : ∀ f g, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g → IsFinF ψ θ ε A B (f + g) := by
    intro f g hf hg
    refine ⟨GlobalTheory.OrientedHeis.theta_add hf.1 hg.1, fun τ z => ?_⟩
    rw [GlobalTheory.FockIndep.annih_add hψ hθ τ _ z hf.1 hg.1, hf.2 τ z, hg.2 τ z, add_zero]
  have h0 : IsFinF ψ θ ε A B 0 := by
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, fun τ z => ?_⟩
    have h := GlobalTheory.FockIndep.annih_smul hψ hθ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ)) z 0
      (GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := sgn ε M) (T := X))
    simpa only [zero_smul] using h
  refine ⟨h0, hadd, hsm, fun f g P hf hg => ?_, fun c f P hf => ?_⟩
  · have h := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ (sgn ε M) X hψ hθ (frSgn ε A).cart A.onb B.cart B.onb 1 hf.1 hg.1 P
    rw [one_smul, one_smul] at h
    exact h
  · have h := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ (sgn ε M) X hψ hθ (frSgn ε A).cart A.onb B.cart B.onb c hf.1
      h0.1 P
    rw [add_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ _ _ hψ hθ, add_zero] at h
    exact h

end GlobalTheory.FinFockLin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAbovePlaceOfTrivialUnits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnrOverPlace

theorem unrAt_of_unramAt : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F),
    IsPlaceIdem D v ε → GlobalTheory.WeilParts.UnramAt ε χ → ∀ w : HeightOneSpectrum (𝓞 D.host.E),
    w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w := by
  intro D χ v ε hε hu w hw x hx
  obtain ⟨h1, h2⟩ := (GlobalTheory.LFun.EulerTie.isUnitAt_iff w x).1 hx
  have hc := GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E)
  obtain ⟨k0, k1, -⟩ := GlobalTheory.CMPrimeIdele.place_comp hc hε
  have key : χ (GlobalTheory.LFun.locIdele D.host.F w x) = 1 := by
    refine hu _ ?_ ((GlobalTheory.LFun.EulerTie.locIdele_int_iff w x).2 h1) (by
      rw [← map_inv]; exact (GlobalTheory.LFun.EulerTie.locIdele_int_iff w x⁻¹).2 h2)
    refine hc.ext' ?_ fun Q ↦ ?_
    · have k0' : GlobalTheory.CMPrimeIdele.infPart D.host.F D.host.E (algebraMap (AF D.host.F) (AE D) ε) = 0 := k0
      have k2 : GlobalTheory.CMPrimeIdele.infPart D.host.F D.host.E ((GlobalTheory.LFun.locIdele D.host.F w x : AE D) - 1) = 0 := by
        rw [map_sub, (GlobalTheory.LFun.EulerTie.parts_locIdele w x).1, map_one, sub_self]
      rw [map_mul, k0', zero_mul, k2]
    · rw [GlobalTheory.CMPrimeIdele.ev_mul]
      by_cases hQ : Q = w
      · subst hQ
        rw [k1 Q hw, one_mul]
      · have e : GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E ((GlobalTheory.LFun.locIdele D.host.F w x : AE D) - 1) Q = 0 := by
          rw [map_sub, map_one]
          show GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E (GlobalTheory.LFun.locIdele D.host.F w x : AE D) Q - 1 = 0
          rw [GlobalTheory.LFun.EulerTie.finComp_locIdele_ne hQ, sub_self]
        rw [e, mul_zero]
  show Circle.toUnits (χ (GlobalTheory.LFun.locIdele D.host.F w x)) = 1
  rw [key, map_one]

end GlobalTheory.UnrOverPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAtCofinitelyManyPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeFinRam

theorem finite_ramified : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ →
    {w : HeightOneSpectrum (𝓞 D.host.E) | ¬ GlobalTheory.LFun.UnrAt χ w}.Finite := by
  intro D χ hχ
  obtain ⟨H, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D χ hχ
  refine (GlobalTheory.Mem.UnrAe.finite_ramified H).subset fun w hw => ?_
  exact fun h => hw ((GlobalTheory.LFun.unrAt_iff_of_chrEq hH w).2 h)

end GlobalTheory.HeckeFinRam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicIntegralsDetermineThetaMeanProductsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicIntegrals_determine_thetaMean_products : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range μ 𝓨 → ∀ F₁ F₁' F₂ F₂' : WO V W → ℂ, IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₁' → IsThetaFunO ψ V W F₂ → IsThetaFunO ψ V W F₂' → (∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ w : WO V W, (∀ y : Mx D a b, symplO V W w (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₁ u * star (F₁' u) ∂ν) ∂μ = ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₂ u * star (F₂' u) ∂ν) ∂μ) → GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁' 0) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂' 0) := by
  first | exact @GlobalTheory.IsoMean.meanX_prod_zero_eq | exact GlobalTheory.IsoMean.meanX_prod_zero_eq | (intros; apply GlobalTheory.IsoMean.meanX_prod_zero_eq <;> assumption)
end

