module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0335
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedProductDropZeroFactors
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd.ProdDrop

section Blocks

variable (k : Type) [Field k] {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N) (o : Fin r' → Fin r)
  (ho : StrictMono o) (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o) (hd' : ∑ a, d (o a) = N)

include ho hz

theorem mem_parab_drop (g : GL (Fin N) k) :
    g ∈ parab k (stdBlocks d hd) ↔ g ∈ parab k (stdBlocks (fun a => d (o a)) hd') := by
  have hE := GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty d hd o ho hz hd'
  rw [mem_parab_iff, mem_parab_iff]
  constructor
  · intro h a b i j hab
    rw [hE, hE]
    exact h _ _ i j (ho hab)
  · intro h a b i j hab
    obtain ⟨a, rfl⟩ := hz a (Nat.pos_iff_ne_zero.1 (Fin.pos i))
    obtain ⟨b, rfl⟩ := hz b (Nat.pos_iff_ne_zero.1 (Fin.pos j))
    have := h a b i j (ho.lt_iff_lt.1 hab)
    rwa [hE, hE] at this

theorem dropHom_leviProj (p : parab k (stdBlocks d hd)) (q : parab k (stdBlocks (fun a => d (o a)) hd'))
    (h : (p : GL (Fin N) k) = q) :
    dropHom d o (leviProj k (stdBlocks d hd) p) = leviProj k (stdBlocks (fun a => d (o a)) hd') q := by
  have hE := GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty d hd o ho hz hd'
  funext a
  ext i j
  show (leviProj k (stdBlocks d hd) p (o a) : Matrix _ _ k) i j = _
  rw [leviProj_apply, leviProj_apply, hE, hE, h]

theorem modExp_drop (a : Fin r') :
    modExp (fun j => Fin (d j)) (o a) = modExp (fun b => Fin (d (o b))) a := by
  have h0 : ∀ j, j ∉ Set.range o → d j = 0 := fun j hj => by_contra fun h => hj (hz j h)
  unfold modExp
  simp only [Fintype.card_fin, Finset.sum_filter]
  congr 1
  · refine (Fintype.sum_of_injective o ho.injective _ _ (fun j hj => ?_) fun b => ?_).symm
    · simp [h0 j hj]
    · simp [ho.lt_iff_lt]
  · refine (Fintype.sum_of_injective o ho.injective _ _ (fun j hj => ?_) fun b => ?_).symm
    · simp [h0 j hj]
    · simp [ho.lt_iff_lt]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N) (o : Fin r' → Fin r)
  (ho : StrictMono o) (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o) (hd' : ∑ a, d (o a) = N)


include ho hz in
theorem deltaHalf_drop (g : Levi k fun j => Fin (d j)) :
    deltaHalf k (fun j => Fin (d j)) g = deltaHalf k (fun a => Fin (d (o a))) (dropHom d o g) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine (Fintype.prod_of_injective o ho.injective _ _ (fun j hj => ?_) fun a => ?_).symm
  · have hj0 : d j = 0 := by_contra fun h => hj (hz j h)
    have : IsEmpty (Fin (d j)) := by rw [hj0]; infer_instance
    have h1 : Matrix.GeneralLinearGroup.det (g j) = 1 := Units.ext (by simp [Matrix.det_isEmpty])
    rw [h1, map_one]
  · rw [modExp_drop d o ho hz]
    rfl


include ho hz in
theorem parInd_comp_dropHom_equiv {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Levi k fun a => Fin (d (o a))) W) :
    Nonempty ((parInd (stdBlocks d hd) (τ.comp (dropHom d o) : Representation ℂ (Levi k fun j => Fin (d j)) W)).Equiv
      (parInd (stdBlocks (fun a => d (o a)) hd') τ)) := by
  have key : ∀ (p : parab k (stdBlocks d hd)) (q : parab k (stdBlocks (fun a => d (o a)) hd')),
      (p : GL (Fin N) k) = q →
      twist (τ.comp (dropHom d o) : Representation ℂ (Levi k fun j => Fin (d j)) W) (deltaHalf k _)
          (leviProj k (stdBlocks d hd) p) =
        twist τ (deltaHalf k _) (leviProj k (stdBlocks (fun a => d (o a)) hd') q) := fun p q h => by
    refine LinearMap.ext fun v => ?_
    rw [twist_apply, twist_apply, deltaHalf_drop d o ho hz, dropHom_leviProj k d hd o ho hz hd' p q h]
    show _ • τ (dropHom d o _) v = _
    rw [dropHom_leviProj k d hd o ho hz hd' p q h]
  refine Placing.smInd_equiv 1
    (fun q => ⟨⟨q.1, (mem_parab_drop k d hd o ho hz hd' q.1).2 q.2⟩, by simp, key _ _ rfl⟩)
    (fun p => ⟨⟨p.1, (mem_parab_drop k d hd o ho hz hd' p.1).1 p.2⟩, by simp, (key _ _ rfl).symm⟩)

end Local


set_option maxHeartbeats 1000000 in
theorem prodIrr_drop : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N), Nonempty ((prodIrr y hd).Equiv (prodIrr (fun a => y (o a)) hd')) := by
  intro k _ _ _ _ r r' N y hd o ho hz hd'
  obtain ⟨φ⟩ := GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv y o ho hz
  obtain ⟨χ⟩ := parInd_comp_dropHom_equiv (k := k) (fun j => (y j).1) hd o ho hz hd'
    (piTensor fun a => (y (o a)).rep)
  have e1 := parIndEquiv (stdBlocks (fun j => (y j).1) hd) φ
  have e2 := e1.trans χ
  unfold prodIrr multiProd
  exact ⟨e2⟩

end GlobalTheory.CompanionTheory.FineProd.ProdDrop

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterleavingTwoColourEmbedding
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd

namespace GlobalTheory.CompanionTheory.WordProd.Intl

def consEmb {m k : ℕ} (σ : Fin m ↪o Fin k) : Fin (m + 1) ↪o Fin (k + 1) :=
  OrderEmbedding.ofStrictMono
    (Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ)) (by
      intro a b hab
      induction a using Fin.cases with
      | zero =>
        induction b using Fin.cases with
        | zero => exact absurd hab (lt_irrefl _)
        | succ b => simp [Fin.succ_pos]
      | succ a =>
        induction b using Fin.cases with
        | zero => exact absurd hab (Fin.not_lt_zero _)
        | succ b => simpa using hab)

def shiftEmb {m k : ℕ} (σ : Fin m ↪o Fin k) : Fin m ↪o Fin (k + 1) :=
  OrderEmbedding.ofStrictMono (fun a => (σ a).succ) (fun a b h => by simpa using h)

@[simp] theorem consEmb_zero {m k : ℕ} (σ : Fin m ↪o Fin k) : consEmb σ 0 = 0 := by
  first
    | rfl
    | exact Fin.cons_zero (α := fun _ => Fin (k + 1)) _ _
    | (show Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ) 0 = 0; simp)

@[simp] theorem consEmb_succ {m k : ℕ} (σ : Fin m ↪o Fin k) (a : Fin m) :
    consEmb σ a.succ = (σ a).succ := by
  first
    | rfl
    | exact Fin.cons_succ (α := fun _ => Fin (k + 1)) _ _ _
    | (show Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ) a.succ = (σ a).succ; simp)

@[simp] theorem shiftEmb_apply {m k : ℕ} (σ : Fin m ↪o Fin k) (a : Fin m) :
    shiftEmb σ a = (σ a).succ := rfl

theorem zero_mem_range_consEmb {m k : ℕ} (σ : Fin m ↪o Fin k) :
    (0 : Fin (k + 1)) ∈ Set.range (consEmb σ) := ⟨0, consEmb_zero σ⟩

theorem succ_mem_range_consEmb {m k : ℕ} (σ : Fin m ↪o Fin k) (j : Fin k) :
    j.succ ∈ Set.range (consEmb σ) ↔ j ∈ Set.range σ := by
  constructor
  · rintro ⟨a, ha⟩
    cases a using Fin.cases with
    | zero =>
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero] at ha
      exact absurd ha.symm (Fin.succ_ne_zero j)
    | succ a =>
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ] at ha
      exact ⟨a, Fin.succ_injective _ ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a.succ, GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ σ a⟩

theorem succ_mem_range_shiftEmb {m k : ℕ} (σ : Fin m ↪o Fin k) (j : Fin k) :
    j.succ ∈ Set.range (shiftEmb σ) ↔ j ∈ Set.range σ := by
  constructor
  · rintro ⟨a, ha⟩
    rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply] at ha
    exact ⟨a, Fin.succ_injective _ ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply σ a⟩

theorem interleave_embeddings : ∀ {T : Type 1} {u v w : List T}, Zc.Comb.Interleave u v w →
    ∃ (r : Fin w.length → Fin 2) (σ₀ : Fin u.length ↪o Fin w.length)
      (σ₁ : Fin v.length ↪o Fin w.length),
      (∀ j, r j = 0 ↔ j ∈ Set.range σ₀) ∧ (∀ j, r j = 1 ↔ j ∈ Set.range σ₁) ∧
      (∀ a, w.get (σ₀ a) = u.get a) ∧ (∀ a, w.get (σ₁ a) = v.get a) := by
  intro T u v w h
  induction h with
  | nil =>
    refine ⟨fun j => Fin.elim0 j, (OrderIso.refl _).toOrderEmbedding,
      (OrderIso.refl _).toOrderEmbedding, ?_, ?_, ?_, ?_⟩ <;> intro j <;> exact Fin.elim0 j
  | @left a u v w _ ih =>
    obtain ⟨r, σ₀, σ₁, h0, h1, hu, hv⟩ := ih
    refine ⟨(Fin.cons (0 : Fin 2) r : Fin (w.length + 1) → Fin 2), GlobalTheory.CompanionTheory.WordProd.Intl.consEmb σ₀,
      GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb σ₁, ?_, ?_, ?_, ?_⟩
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero, true_iff]
        exact GlobalTheory.CompanionTheory.WordProd.Intl.zero_mem_range_consEmb σ₀
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_consEmb]
        exact h0 j
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero]
        constructor
        · intro hc
          exact absurd hc (by decide)
        · rintro ⟨x, hx⟩
          rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply] at hx
          exact absurd hx (Fin.succ_ne_zero _)
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_shiftEmb]
        exact h1 j
    · intro x
      obtain rfl | ⟨x, rfl⟩ := Fin.eq_zero_or_eq_succ (n := u.length) x
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero]
        simp
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ]
        first
          | exact hu x
          | simpa using hu x
    · intro x
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply]
      first
        | exact hv x
        | simpa using hv x
  | @right a u v w _ ih =>
    obtain ⟨r, σ₀, σ₁, h0, h1, hu, hv⟩ := ih
    refine ⟨(Fin.cons (1 : Fin 2) r : Fin (w.length + 1) → Fin 2), GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb σ₀,
      GlobalTheory.CompanionTheory.WordProd.Intl.consEmb σ₁, ?_, ?_, ?_, ?_⟩
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero]
        constructor
        · intro hc
          exact absurd hc (by decide)
        · rintro ⟨x, hx⟩
          rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply] at hx
          exact absurd hx (Fin.succ_ne_zero _)
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_shiftEmb]
        exact h0 j
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero, true_iff]
        exact GlobalTheory.CompanionTheory.WordProd.Intl.zero_mem_range_consEmb σ₁
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_consEmb]
        exact h1 j
    · intro x
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply]
      first
        | exact hu x
        | simpa using hu x
    · intro x
      obtain rfl | ⟨x, rfl⟩ := Fin.eq_zero_or_eq_succ (n := v.length) x
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero]
        simp
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ]
        first
          | exact hv x
          | simpa using hv x

end GlobalTheory.CompanionTheory.WordProd.Intl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleOfDiscreteSeriesDatum
section
noncomputable section

open Finset Matrix

namespace GlobalTheory.CompanionTheory.RgDsHilb

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.RgDs PositivityTheory.RgDs.Hilb

variable {n : ℕ}

theorem isKTypeOf_map_of_injOn {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Λ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : Formalism.MainNotions.S.IsKTypeOf ε σ Λ S) (A : H →ₗ[ℂ] H)
    (hcomm : ∀ k ∈ Kset ε, ∀ v, σ k (A v) = A (σ k v))
    (hinj : ∀ w ∈ S, A w = 0 → w = 0) :
    Formalism.MainNotions.S.IsKTypeOf ε σ Λ (S.map A) := by
  haveI : FiniteDimensional ℂ S := hS.1
  have hirr : ∀ S' : Submodule ℂ H, S' ≤ S.map A → Formalism.MainNotions.S.IsKStableOn ε σ S' →
      S' = ⊥ ∨ S' = S.map A := by
    intro S' hS' hK'
    have hTK : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ S'.comap A) := by
      intro g hg v hv
      rw [Submodule.mem_inf] at hv ⊢
      refine ⟨hS.2.1 g hg v hv.1, ?_⟩
      show A (σ g v) ∈ S'
      rw [← hcomm g hg v]
      exact hK' g hg _ hv.2
    rcases hS.2.2.1 (S ⊓ S'.comap A) inf_le_left hTK with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hS' hx
      have hwT : w ∈ S ⊓ S'.comap A := Submodule.mem_inf.2 ⟨hw, hx⟩
      rw [h] at hwT
      rw [(Submodule.mem_bot ℂ).1 hwT, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨w, hw, rfl⟩
      have hwT : w ∈ S ⊓ S'.comap A := by rw [h]; exact hw
      exact (Submodule.mem_inf.1 hwT).2
  refine ⟨inferInstance, ?_, hirr, ?_, ?_⟩
  · rintro g hg _ ⟨w, hw, rfl⟩
    exact ⟨σ g w, hS.2.1 g hg w hw, (hcomm g hg w).symm⟩
  · obtain ⟨v, hv, hv0, hwt⟩ := hS.2.2.2.1
    refine ⟨A v, ⟨v, hv, rfl⟩, fun h => hv0 (hinj v hv h), ?_⟩
    intro θ hθ
    rw [hcomm _ hθ, hwt θ hθ, map_smul]
  · rintro μ _ ⟨w, hw, rfl⟩ hne hwt
    refine hS.2.2.2.2 μ w hw (fun h => hne (by rw [h, map_zero])) ?_
    intro θ hθ
    have h1 : A (σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) w -
        Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • w) = 0 := by
      rw [map_sub, map_smul, ← hcomm _ hθ, hwt θ hθ, sub_self]
    have h2 := hinj _ (Submodule.sub_mem _ (hS.2.1 _ hθ w hw) (Submodule.smul_mem _ _ hw)) h1
    exact sub_eq_zero.1 h2

theorem stepIrred_of_stepDatum : StepDatum → StepIrred := by
  intro hDatum n ε lam T Ψ hP _hst huniq W hWle hWc hWG
  classical
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV1 : Formalism.MainNotions.S.IsKTypeOf ε (rreg ε) (lowK ε lam) (V1 ε Ψ) := hDatum n ε lam T Ψ hP
  have : CompleteSpace W := hWc.completeSpace_coe
  have hWo : ∀ g ∈ UJset ε, ∀ x ∈ Wᗮ, rreg ε g x ∈ Wᗮ := by
    intro g hg
    obtain ⟨g', hg', hgg⟩ := UnitaryGroupOfForm.inv_mem_UJ hg
    exact UnitaryGroupOfForm.orth_stable hσ hg hg' hgg W (hWG g' hg')
  have hK : Formalism.MainNotions.S.IsKStableOn ε (rreg ε) (V1 ε Ψ ⊓ Wᗮ) := by
    intro k hk x hx
    exact ⟨hV1.2.1 k hk x hx.1, hWo k (UnitaryGroupOfForm.K_mem_UJ hk) x hx.2⟩
  have hmem : ∀ v ∈ datumV ε Ψ T.w, ((v : smD ε (rreg ε)) : L2 ε) ∈ V1 ε Ψ :=
    fun v hv => Submodule.mem_map_of_mem hv
  rcases hV1.2.2.1 (V1 ε Ψ ⊓ Wᗮ) inf_le_left hK with h0 | hV'
  · right
    refine le_antisymm hWle (UnitaryGroupOfForm.closGen_le hD W hWc hWG _ ?_)
    have hcomm : ∀ k ∈ Kset ε, ∀ v, rreg ε k (W.starProjection.toLinearMap v) =
        W.starProjection.toLinearMap (rreg ε k v) := by
      intro k hk v
      have hkU := UnitaryGroupOfForm.K_mem_UJ hk
      exact (UnitaryGroupOfForm.proj_comm W (rreg ε k) (hWG k hkU) (hWo k hkU) v).symm
    have hinj : ∀ w ∈ V1 ε Ψ, W.starProjection.toLinearMap w = 0 → w = 0 := by
      intro w hw h
      have hwo : w ∈ Wᗮ := by
        have := W.sub_starProjection_mem_orthogonal w
        have h' : W.starProjection w = 0 := h
        rwa [h', sub_zero] at this
      have : w ∈ V1 ε Ψ ⊓ Wᗮ := ⟨hw, hwo⟩
      rw [h0] at this
      exact (Submodule.mem_bot ℂ).1 this
    have hle : (V1 ε Ψ).map W.starProjection.toLinearMap ≤ W := by
      rintro _ ⟨w, -, rfl⟩
      exact W.starProjection_apply_mem w
    have heq := huniq _ (hle.trans hWle) (isKTypeOf_map_of_injOn hV1 _ hcomm hinj)
    intro v hv
    have hv' : ((v : smD ε (rreg ε)) : L2 ε) ∈ (V1 ε Ψ).map W.starProjection.toLinearMap := by
      rw [heq]; exact hmem v hv
    exact hle hv'
  · left
    have hle : Hlam ε Ψ T.w ≤ Wᗮ :=
      UnitaryGroupOfForm.closGen_le hD Wᗮ (Submodule.isClosed_orthogonal W) hWo _
        (fun v hv => (show ((v : smD ε (rreg ε)) : L2 ε) ∈ V1 ε Ψ ⊓ Wᗮ by
          rw [hV']; exact hmem v hv).2)
    rw [eq_bot_iff, ← Submodule.inf_orthogonal_eq_bot W]
    exact le_inf le_rfl (hWle.trans hle)

end GlobalTheory.CompanionTheory.RgDsHilb
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCount

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

def m0Z (lam : Fin n → ℤ) : Fin n → ℤ := fun a => 2 * lam a + ((n : ℤ) - 1) - 2 * ((a : ℕ) : ℤ)

def wtR (μ : Fin n → ℤ) : Fin n → ℝ := fun a => (μ a : ℝ)

def DomLE (ν m : Fin n → ℝ) : Prop :=
  (∀ k : ℕ, ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), ν a ≤ ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), m a) ∧
    ∑ a, ν a = ∑ a, m a

def wtDual (E : KMod n) (μ : Fin n → ℤ) : Submodule ℂ (E.V →L[ℂ] ℂ) where
  carrier := {ξ | ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z →
    ξ ∘L E.ρ k⁻¹ = (∏ a, z a ^ μ a) • ξ}
  add_mem' {x y} hx hy k z hk := by
    rw [ContinuousLinearMap.add_comp, hx k z hk, hy k z hk, smul_add]
  zero_mem' k z _ := by simp
  smul_mem' c x hx k z hk := by
    rw [ContinuousLinearMap.smul_comp, hx k z hk, smul_comm]

def IsCliff {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ) : Prop :=
  (∀ a b d e, c a b * c d e + c d e * c a b = if a = e ∧ b = d then (2 : Matrix ι ι ℂ) else 0) ∧
    ∀ a b, (c a b)ᴴ = c b a

def spinM {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ∑ e, c a e * c e b - if a = b then ((n : ℂ) / 2) • (1 : Matrix ι ι ℂ) else 0

def yF {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Kf : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) :
    Module.End ℂ (ι → V) where
  toFun x := fun i => Kf a b (x i) + ∑ j, spinM c a b i j • x j
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, map_add (f := _), smul_add, Finset.sum_add_distrib]
    abel
  map_smul' s x := by
    funext i
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

end GlobalTheory.CompanionTheory.RealCount
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLSegSingle
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.LocGL

theorem isLSeg_single (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) : IsLSeg (Segment.single ρ hρ) ρ.rep := by
  have hterm : ((Segment.single ρ hρ).term : Fin 1 → IrrGL (k := k)) = fun _ => ρ := by
    funext a
    have ha : (a : ℕ) = 0 := by
      have h1 : (a : ℕ) < 1 := a.isLt
      omega
    show (Segment.single ρ hρ).first.nu ((a : ℕ) : ℂ) = ρ
    rw [ha, Nat.cast_zero, show (Segment.single ρ hρ).first = ρ from Segment.first_ofFirst ρ hρ 1 one_pos,
      IrrGL.nu_zero]
  have key : ∀ x : Fin 1 → IrrGL (k := k), x = (fun _ => ρ) → ∀ hd : ∑ a, (x a).1 = ρ.1,
      IsCosocle ρ.rep (prodIrr x hd) := by
    intro x hx hd
    subst hx
    obtain ⟨φ⟩ := nonempty_equiv_prodIrr_one ρ hd
    exact (isCosocle_self ρ.2.rep.irr).of_equiv (Representation.Equiv.refl _) φ
  have hd : ∑ a : Fin 1, ((Segment.single ρ hρ).term a).1 = ρ.1 := by
    rw [hterm]
    simp
  exact ⟨hd, key _ hterm hd⟩

end GlobalTheory.CompanionTheory.LocGL
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingMemLeviStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_embedding_mem_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (g : Levi k (fun a => Fin (d a))), leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd) := by
  intro k _ _ _ _ h N d hd g
  rw [GroundTheory.Automorphic.Parabolic.mem_levi]
  intro i j hij
  obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective j
  have hab : a ≠ b := by
    simpa [Zl.JC.blockIdx] using hij
  exact leviEmb_apply_ne k (stdBlocks d hd) g hab x y
end

