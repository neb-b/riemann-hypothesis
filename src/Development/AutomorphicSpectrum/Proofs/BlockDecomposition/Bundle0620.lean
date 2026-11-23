module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.FinCut
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
public import GroundTheory.AutomorphicForms.Bundle0024

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionProductRankZeroLeft
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.CompanionTheory.BZRes
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibRes0Left

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def evalTop (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : Representation ℂ H W) (hσ : IsSmooth σ) :
    smoothPart (ind H σ) ≃ₗ[ℂ] W where
  toFun f := f.1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨⟨fun g => σ ⟨g, hH g⟩ w, by
      intro h g
      show σ ⟨(h : G) * g, hH _⟩ w = σ h (σ ⟨g, hH g⟩ w)
      rw [← Module.End.mul_apply, ← map_mul]
      rfl⟩, by
      have hop : IsOpen {g : G | σ ⟨g, hH g⟩ w = w} :=
        (hσ w).preimage (continuous_id.subtype_mk hH)
      have h1 : (1 : G) ∈ {g : G | σ ⟨g, hH g⟩ w = w} := by
        show σ ⟨1, hH 1⟩ w = w
        rw [show (⟨1, hH 1⟩ : H) = 1 from rfl, map_one, Module.End.one_apply]
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset (hop.mem_nhds h1) fun g hg => ?_)
      refine Subtype.ext (funext fun x => ?_)
      show σ ⟨x * g, hH _⟩ w = σ ⟨x, hH x⟩ w
      rw [show (⟨x * g, hH _⟩ : H) = ⟨x, hH x⟩ * ⟨g, hH g⟩ from rfl, map_mul, Module.End.mul_apply]
      exact congrArg _ hg⟩
  left_inv f := by
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    show σ ⟨g, hH g⟩ (f.1.1 1) = f.1.1 g
    have := f.1.2 ⟨g, hH g⟩ 1
    rw [← this, mul_one]
  right_inv w := by
    show σ ⟨1, hH 1⟩ w = w
    rw [show (⟨1, hH 1⟩ : H) = 1 from rfl, map_one, Module.End.one_apply]

theorem mem_cIndSpace_top (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : Representation ℂ H W) (f : smoothPart (ind H σ)) :
    f ∈ cIndSpace H σ := by
  exact ⟨{1}, isCompact_singleton, fun g _ => ⟨g, hH g, 1, Set.mem_singleton 1, (mul_one g).symm⟩⟩

def cTop (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : Representation ℂ H W) :
    cIndSpace H σ ≃ₗ[ℂ] smoothPart (ind H σ) where
  toFun f := f.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f, mem_cIndSpace_top H hH σ f⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {P W₂ : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [AddCommGroup W₂] [Module ℂ W₂]

theorem equiv_of_top (ι : P →* G) (hι : Continuous ι) (Q : Subgroup G) (H : Subgroup P) (hQ : ∀ g, g ∈ Q)
    (hH : ∀ p, p ∈ H) (σ : Representation ℂ Q W) (τ : Representation ℂ H W₂) (E : W ≃ₗ[ℂ] W₂) (hσ : IsSmooth σ)
    (hE : ∀ (h : H) (v : W), τ h (E v) = E (σ ⟨ι h, hQ _⟩ v)) :
    Nonempty (Representation.Equiv ((smInd Q σ).comp ι) (cInd H τ)) := by
  have hτ : IsSmooth τ := by
    intro w
    obtain ⟨v, rfl⟩ := E.surjective w
    have hset : {h : H | τ h (E v) = E v} =
        (fun h : H => (⟨ι h, hQ _⟩ : Q)) ⁻¹' {q : Q | σ q v = v} := by
      ext h
      show τ h (E v) = E v ↔ σ ⟨ι h, hQ _⟩ v = v
      rw [hE h v]
      exact E.injective.eq_iff
    rw [hset]
    exact (hσ v).preimage ((hι.comp continuous_subtype_val).subtype_mk _)
  let L : smoothPart (ind Q σ) ≃ₗ[ℂ] cIndSpace H τ :=
    ((evalTop Q hQ σ hσ).trans E).trans ((evalTop H hH τ hτ).symm.trans (cTop H hH τ).symm)
  refine ⟨Representation.Equiv.mk L fun p => ?_⟩
  refine LinearMap.ext fun f => ?_
  refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => ?_)))
  show τ ⟨x, hH x⟩ (E (f.1.1 (1 * ι p))) = τ ⟨x * p, hH _⟩ (E (f.1.1 1))
  have hf : f.1.1 (ι p) = σ ⟨ι p, hQ _⟩ (f.1.1 1) := by
    have := f.1.2 ⟨ι p, hQ _⟩ 1
    rw [mul_one] at this
    exact this
  rw [one_mul, hf, show E (σ ⟨ι p, hQ _⟩ (f.1.1 1)) = τ ⟨p, hH p⟩ (E (f.1.1 1)) from (hE ⟨p, hH p⟩ _).symm,
    ← Module.End.mul_apply, ← map_mul]
  rfl

end Abstract

section Concrete

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem hgp_twist_tE {m j : ℕ}
    (π₁ : Representation ℂ (GL (Fin m) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : MirabolicParabolic k m j)
    (hq : ((g : Mir k (m + j)) : GL (Fin (m + j + 1)) k) ∈
      parab k (two (stdSum (rfl : m + (j + 1) = m + j + 1))))
    (v : ⨂[ℂ] x, TwoT V W x) :
    ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k m) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((m : ℕ) : ℝ) / 2)).ρ).comp (gpProj k m j)) g (tE V W v) =
      tE V W (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩ v) := by
  set L := leviProj k (two (stdSum (rfl : m + (j + 1) = m + j + 1))) ⟨_, hq⟩ with hL
  have hL2 : leviTwo k (Fin m) (Fin (j + 1)) (L false, L true) = L := by
    funext b
    cases b <;> rfl
  have hδ := GlobalTheory.SmGL.deltaHalf_two (k := k) (a := Fin m) (b := Fin (j + 1)) (L false, L true)
  rw [hL2] at hδ
  have hc : (((dpow m (((j + 1 : ℕ) : ℝ) / 2)) (L false) : ℂˣ) : ℂ) *
      (((dpow (j + 1) (-((m : ℕ) : ℝ) / 2)) (L true) : ℂˣ) : ℂ) =
      ((deltaHalf k (Two (Fin m) (Fin (j + 1))) L : ℂˣ) : ℂ) := by
    rw [hδ, Units.val_mul]
    simp only [dpow, GlobalTheory.SmGL.detChar_apply, Fintype.card_fin]
    congr 4 <;> push_cast <;> ring
  have key : ∀ x : (b : Bool) → TwoT V W b,
      ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k m) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((m : ℕ) : ℝ) / 2)).ρ).comp (gpProj k m j)) g
          (tE V W (PiTensorProduct.tprod ℂ x)) =
      tE V W (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) := by
    intro x
    have e1 : tE V W (PiTensorProduct.tprod ℂ x) = x false ⊗ₜ[ℂ] x true :=
      GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod x
    have e2 : sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x) =
        ((deltaHalf k (Two (Fin m) (Fin (j + 1))) L : ℂˣ) : ℂ) •
          PiTensorProduct.tprod ℂ (fun b => twoRep π₁ π₂ b (L b) (x b)) := by
      show ((deltaHalf k (Two (Fin m) (Fin (j + 1))) L : ℂˣ) : ℂ) •
          (piTensor (twoRep π₁ π₂) L) (PiTensorProduct.tprod ℂ x) = _
      rw [GlobalTheory.SmGL.piTensor_tprod]
    have e3 : tE V W (PiTensorProduct.tprod ℂ (fun b => twoRep π₁ π₂ b (L b) (x b))) =
        π₁ (L false) (x false) ⊗ₜ[ℂ] π₂ (L true) (x true) :=
      GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod _
    rw [e1, e2, map_smul, e3, MonoidHom.comp_apply]
    erw [GlobalTheory.SmGL.extTensor_tmul]
    show ((((dpow m (((j + 1 : ℕ) : ℝ) / 2)) (L false) : ℂˣ) : ℂ) • π₁ (L false) (x false)) ⊗ₜ[ℂ]
        ((((dpow (j + 1) (-((m : ℕ) : ℝ) / 2)) (L true) : ℂˣ) : ℂ) • π₂ (L true) (x true)) = _
    rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, hc]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [LinearEquiv.map_smul (tE V W) r,
      LinearMap.map_smul (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩) r,
      LinearEquiv.map_smul (tE V W), ← key x]
    exact LinearMap.map_smul _ _ _
  | add a b ha hb =>
    rw [LinearEquiv.map_add (tE V W) a b,
      LinearMap.map_add (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩) a b,
      LinearEquiv.map_add (tE V W), ← ha, ← hb]
    exact LinearMap.map_add _ _ _

theorem mem_parab_zero {j : ℕ} (g : GL (Fin (0 + j + 1)) k) :
    g ∈ parab k (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1))) := by
  intro a b hab
  have key : ∀ x : Fin (0 + j + 1), GlobalTheory.SmGL.blk (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1))) x = true := by
    intro x
    unfold GlobalTheory.SmGL.blk
    rcases (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1))).symm x with ⟨b, y⟩
    cases b
    · exact Fin.elim0 y
    · rfl
  rw [key, key] at hab
  exact absurd hab (lt_irrefl _)

theorem isSmooth_sQ {r t N : ℕ} (h : r + t = N) {π₁ : Representation ℂ (GL (Fin r) k) V}
    {π₂ : Representation ℂ (GL (Fin t) k) W} (h₁ : IsSmooth π₁) (h₂ : IsSmooth π₂) : IsSmooth (sQ h π₁ π₂) := by
  refine GlobalTheory.SmGL.isSmooth_comp (GlobalTheory.SmGL.isSmooth_twist (GlobalTheory.SmGL.isSmooth_piTensor fun b => ?_)
    (GlobalTheory.SmGL.isSmoothChar_deltaHalf k)) _ ?_
  · cases b
    · exact h₁
    · exact h₂
  · refine continuous_pi fun b => Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_submatrix
        (fun i => (two (stdSum h)) ⟨b, i⟩) (fun i => (two (stdSum h)) ⟨b, i⟩)
    · have hinv : Continuous fun p : parab k (two (stdSum h)) =>
          (((p⁻¹ : parab k (two (stdSum h))) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) :=
        (Units.continuous_val.comp continuous_subtype_val).comp continuous_inv
      refine (hinv.matrix_submatrix (fun i => (two (stdSum h)) ⟨b, i⟩)
        (fun i => (two (stdSum h)) ⟨b, i⟩)).congr fun p => ?_
      rw [← Pi.inv_apply, ← map_inv]
      rfl

theorem gres_prod_zero_left (j n : ℕ) (π₁ : GRep k 0) (π₂ : GRep k (j + 1)) (h : 0 + (j + 1) = n + 1) (h' : 0 + j = n)
    (h₁ : IsSmooth π₁.ρ) (h₂ : IsSmooth π₂.ρ) :
    MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodGPn π₁ (gres π₂))) := by
  subst h'
  exact equiv_of_top (Mir k (0 + j)).subtype continuous_subtype_val
    (parab k (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1)))) (MirabolicParabolic k 0 j)
    (fun g => mem_parab_zero g) (fun p => mem_parab_zero (p : GL (Fin (0 + j + 1)) k))
    (sQ (rfl : 0 + (j + 1) = 0 + j + 1) π₁.ρ π₂.ρ)
    ((extTensor (π₁.tw (((j + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres π₂) (-((0 : ℕ) : ℝ) / 2)).ρ).comp (gpProj k 0 j))
    (tE π₁.V π₂.V) (isSmooth_sQ rfl h₁ h₂)
    (fun hh v => hgp_twist_tE π₁.ρ π₂.ρ hh (mem_parab_zero _) v)

theorem gres_prod_zero_left' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (j n : ℕ) (π₁ : GRep k 0) (π₂ : GRep k (j + 1)) (h : 0 + (j + 1) = n + 1) (h' : 0 + j = n),
    IsSmooth π₁.ρ → IsSmooth π₂.ρ → MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodGPn π₁ (gres π₂))) := by
  intro k _ _ _ _ j n π₁ π₂ h h' h₁ h₂
  exact gres_prod_zero_left j n π₁ π₂ h h' h₁ h₂

end Concrete

end GlobalTheory.CompanionTheory.LeibRes0Left

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShapeMemBounded
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.One PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.F.F5

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.FinFamAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def Cov (S : Set (Pre E n)) : Prop :=
  ∃ (k : ℕ) (D : Fin k → Pre E n), ∀ D' ∈ S, ∃ j, PreEquiv (D j) D'

theorem cov_of_rel {S : Set (Pre E n)} {ι : Type*} [Finite ι] (P : ι → Pre E n → Prop)
    (h1 : ∀ D ∈ S, ∃ a, P a D)
    (h2 : ∀ a, ∀ D₁ ∈ S, ∀ D₂ ∈ S, P a D₁ → P a D₂ → PreEquiv D₁ D₂) : Cov S := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨D₀, -⟩ := hS
    let e := Finite.equivFin ι
    refine ⟨Nat.card ι, fun j => if h : ∃ D ∈ S, P (e.symm j) D then h.choose else D₀, ?_⟩
    intro D' hD'
    obtain ⟨a, ha⟩ := h1 D' hD'
    have hex : ∃ D ∈ S, P (e.symm (e a)) D := ⟨D', hD', by rw [Equiv.symm_apply_apply]; exact ha⟩
    refine ⟨e a, ?_⟩
    show PreEquiv (if h : ∃ D ∈ S, P (e.symm (e a)) D then h.choose else D₀) D'
    rw [dite_eq_left hex]
    obtain ⟨hmem, hP⟩ := hex.choose_spec
    exact h2 _ _ hmem _ hD' hP (by rw [Equiv.symm_apply_apply]; exact ha)
  · exact ⟨0, Fin.elim0, fun D' hD' => (hS ⟨D', hD'⟩).elim⟩

theorem cov_of_cover {S : Set (Pre E n)} {ι : Type*} [Finite ι] (A : ι → Set (Pre E n))
    (hA : ∀ a, Cov (A a)) (hS : ∀ D ∈ S, ∃ a, D ∈ A a) : Cov S := by
  classical
  choose k D hD using fun a => (hA a : ∃ (k : ℕ) (D : Fin k → Pre E n), ∀ D' ∈ A a, ∃ j, PreEquiv (D j) D')
  let e := Finite.equivFin (Σ a, Fin (k a))
  refine ⟨Nat.card (Σ a, Fin (k a)), fun j => D (e.symm j).1 (e.symm j).2, ?_⟩
  intro D' hD'
  obtain ⟨a, ha⟩ := hS D' hD'
  obtain ⟨j, hj⟩ := hD a D' ha
  refine ⟨e ⟨a, j⟩, ?_⟩
  show PreEquiv (D (e.symm (e ⟨a, j⟩)).1 (e.symm (e ⟨a, j⟩)).2) D'
  rw [Equiv.symm_apply_apply]
  exact hj

abbrev Shape (E : Type) [Field E] : Type :=
  Σ c : ℕ, (Fin c → ℕ) × (Fin c → (E →+* ℂ) → Multiset ℂ)

def shape (D : Pre E n) : Shape E := ⟨D.c, D.N, D.m⟩

def bounded (E : Type) [Field E] (n : ℕ) (m : (E →+* ℂ) → Multiset ℂ) : Set (Shape E) :=
  {t | t.1 ≤ n ∧ (∀ i, t.2.1 i ≤ n) ∧ ∀ i τ, t.2.2 i τ ≤ m τ}

theorem finite_le (s : Multiset ℂ) : {x : Multiset ℂ | x ≤ s}.Finite := by
  exact (Multiset.finite_toSet s.powerset).subset fun x hx => Multiset.mem_powerset.mpr hx

theorem bounded_finite (n : ℕ) (m : (E →+* ℂ) → Multiset ℂ) : (bounded E n m).Finite := by
  refine ((Set.finite_Iic n).biUnion fun c _ =>
    (((Set.Finite.pi fun _ : Fin c => Set.finite_Iic n).prod
      (Set.Finite.pi fun _ : Fin c => Set.Finite.pi fun τ => finite_le (m τ))).image
        (fun p => (⟨c, p⟩ : Shape E)))).subset ?_
  rintro ⟨c, N, mm⟩ ⟨hc, hN, hm⟩
  exact Set.mem_iUnion₂.mpr ⟨c, hc, ⟨(N, mm), ⟨fun i _ => hN i, fun i _ τ _ => hm i τ⟩, rfl⟩⟩

theorem shape_mem_bounded (m : (E →+* ℂ) → Multiset ℂ) (D : Pre E n)
    (hm : ∀ τ, ∑ i, D.m i τ = m τ) : shape D ∈ bounded E n m := by
  refine ⟨?_, fun i => ?_, fun i τ => ?_⟩
  · show D.c ≤ n
    calc D.c = ∑ _i : Fin D.c, 1 := by simp
      _ ≤ ∑ i, D.N i := Finset.sum_le_sum fun i _ => D.pos i
      _ = n := D.h
  · show D.N i ≤ n
    exact (Finset.single_le_sum (f := D.N) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans D.h.le
  · show D.m i τ ≤ m τ
    rw [← hm τ]
    exact Finset.single_le_sum (f := fun j => D.m j τ) (fun j _ => Multiset.zero_le _) (Finset.mem_univ i)

theorem cov_fibre (hL : LevelFactor) (hF : FinDiscN)
    (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
    (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) (hK : IsLevel K) (hW : ∀ N, FiniteDimensional ℂ (W N))
    (t : Shape E) :
    Cov {D' : Pre E n | shape D' = t ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) ∧
      ∀ i, HasKType (W (D'.N i)) (D'.V i)} := by
  classical
  obtain ⟨c, N, mm⟩ := t
  by_cases hsum : ∑ i, N i = n
  swap
  · refine ⟨0, Fin.elim0, ?_⟩
    rintro ⟨c', N', h', V', σ', m', pos', disc', loc', inf'⟩ ⟨hsh, -, -⟩
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hsh
    obtain ⟨rfl, -⟩ := Prod.mk.inj (eq_of_heq hh)
    exact absurd h' hsum
  choose Ki hKiopen hKiKGL hKisph using fun w => hL E w c n N hsum (K w) (hK.1 w)
  have hlev : ∀ i : Fin c, IsLevel (fun w => Ki w i) := fun i =>
    ⟨fun w => hKiopen w i, hK.2.mono fun w hw => hKiKGL w hw i⟩
  choose k σs hσs using fun i : Fin c =>
    hF E (N i) (fun w => Ki w i) (W (N i)) (mm i) (hlev i) (hW (N i))
  refine cov_of_rel (ι := (i : Fin c) → Fin (k i))
    (fun a D => ∃ hc : D.c = c, ∀ (i : Fin D.c) w, ∃ hs hi,
      D.cls i w = GlobalTheory.LocGL.IrrGL.of (σs (Fin.cast hc i) (a (Fin.cast hc i)) w).ρ hs hi) ?_ ?_
  · rintro ⟨c', N', h', V', σ', m', pos', disc', loc', inf'⟩ ⟨hsh, hsph, hKt⟩
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hsh
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh)
    choose a ha using fun i => hσs i (V' i) (fun w => σ' i w) (disc' i) (fun w => loc' i w)
      (fun τ => inf' i τ) (fun w => hKisph w (fun j => σ' j w) (hsph w) i) (hKt i)
    exact ⟨a, rfl, fun i w => ⟨_, _, (ha i w).symm⟩⟩
  · rintro a ⟨c₁, N₁, h₁, V₁, σ₁, m₁, pos₁, disc₁, loc₁, inf₁⟩ ⟨hsh₁, -, -⟩
      ⟨c₂, N₂, h₂, V₂, σ₂, m₂, pos₂, disc₂, loc₂, inf₂⟩ ⟨hsh₂, -, -⟩ ⟨hc₁, hP₁⟩ ⟨hc₂, hP₂⟩
    obtain ⟨rfl, hh₁⟩ := Sigma.mk.inj_iff.mp hsh₁
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh₁)
    obtain ⟨rfl, hh₂⟩ := Sigma.mk.inj_iff.mp hsh₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh₂)
    refine ⟨finCongr rfl, fun i w => ?_, fun i τ => rfl⟩
    obtain ⟨hs₁, hi₁, e₁⟩ := hP₁ i w
    obtain ⟨hs₂, hi₂, e₂⟩ := hP₂ i w
    exact e₁.trans e₂.symm

theorem finFamOf : FinFamOf := by
  intro hL hF E _ _ _ n K W m hK hW
  have hS : Cov {D' : Pre E n | (∀ τ, ∑ i, D'.m i τ = m τ) ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) ∧
      ∀ i, HasKType (W (D'.N i)) (D'.V i)} := by
    have hfin := bounded_finite (E := E) n m
    haveI := hfin.to_subtype
    refine cov_of_cover (ι := bounded E n m) (fun t => {D' : Pre E n | shape D' = t.1 ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) ∧
      ∀ i, HasKType (W (D'.N i)) (D'.V i)}) (fun t => cov_fibre hL hF K W hK hW t.1) ?_
    rintro D' ⟨hm, hsph, hKt⟩
    exact ⟨⟨shape D', shape_mem_bounded m D' hm⟩, rfl, hsph, hKt⟩
  obtain ⟨k, D, hD⟩ := hS
  exact ⟨k, D, fun D' hm hsph hKt => hD D' ⟨hm, hsph, hKt⟩⟩

end GlobalTheory.CompanionTheory.FinFamAssembly

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothParabolicInductionProduct
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZRes

theorem isSmooth_sQ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {r t N : ℕ} (h : r + t = N)
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W)
    (h₁ : IsSmooth π₁) (h₂ : IsSmooth π₂) : IsSmooth (sQ h π₁ π₂) := by
  unfold GlobalTheory.CompanionTheory.BZRes.sQ
  refine GlobalTheory.SmGL.isSmooth_comp ?_ _
    (GlobalTheory.SmGL.ProdIrr.continuous_leviProj _)
  refine GlobalTheory.SmGL.isSmooth_twist ?_
    (GlobalTheory.SmGL.isSmoothChar_deltaHalf k)
  refine GlobalTheory.SmGL.isSmooth_piTensor ?_
  intro x
  cases x
  · exact h₁
  · exact h₂

end GlobalTheory.CompanionTheory.BZRes
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientPrincipalSeriesBound
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.HeckeSub

theorem isSatakeParameter_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (α : Fin n → ℂˣ) (X V : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) X), IsSmooth ρ → ∀ (ι : ρ.IntertwiningMap (principalSeries k n (paramChar k α))), Function.Injective ι → ∀ (π : Representation ℂ (GL (Fin n) k) V), IsSubquotient π ρ → ∀ [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k)) [μ.IsHaarMeasure], IsSatakeParameter π μ α := by
  intro k _ _ _ _ n α X V _ _ _ _ ρ hρ ι hι π hπ _ _ μ _ h v hv
  obtain ⟨S, f, hf⟩ := hπ
  have hS : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth (ρ := ρ) ⟨S, .id _, Function.surjective_id⟩ hρ
  obtain ⟨u, rfl⟩ := hf v
  have hfix : ∀ g ∈ GroundTheory.Automorphic.GLnLocal.integralGL k n, π g (f u) = f u := fun g hg =>
    GroundTheory.Automorphic.mem_fixedVectors.1 hv g hg
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hS
    (GroundTheory.Automorphic.GLnLocal.isCompact_integralGL k n) f.toLinearMap u fun g hg => by
      show f (S.toRepresentation g u) = f u
      rw [f.isIntertwining]
      exact hfix g hg
  have hfw' : f w = f u := hfw
  have hw' : w ∈ GroundTheory.Automorphic.fixedVectors S.toRepresentation
      (GroundTheory.Automorphic.GLnLocal.integralGL k n) := by
    simpa [fixed, eig, GroundTheory.Automorphic.fixedVectors] using hw
  let T : S.toRepresentation.IntertwiningMap (principalSeries k n (paramChar k α)) :=
    ⟨ι.toLinearMap ∘ₗ S.toSubmodule.subtype, fun g => by
      refine LinearMap.ext fun x => ?_
      exact ι.isIntertwining _ _ g x⟩
  have hT : Function.Injective T := fun a b e => Subtype.ext (hι e)
  have hTw : T w ∈ GroundTheory.Automorphic.fixedVectors (principalSeries k n (paramChar k α))
      (GroundTheory.Automorphic.GLnLocal.integralGL k n) :=
    GroundTheory.Automorphic.mem_fixedVectors.2 fun g hg => by
      rw [← T.isIntertwining, GroundTheory.Automorphic.mem_fixedVectors.1 hw' g hg]
  have hmem := (h : GroundTheory.Automorphic.HeckeAlgebra μ).mem
  set c := GroundTheory.Automorphic.Spherical.evalAt α (satakeTransform μ h) with hc
  have hPS := isSatakeParameter_principalSeries (F := k) (μ := μ) α h (T w) hTw
  have hact : GroundTheory.Automorphic.heckeAct μ S.toRepresentation (h : GroundTheory.Automorphic.HeckeAlgebra μ) w = c • w := by
    apply hT
    rw [GroundTheory.Automorphic.map_heckeAct T hmem (hS w), hPS, map_smul]
  rw [← hfw', ← GroundTheory.Automorphic.map_heckeAct f hmem (hS w), hact, map_smul]

end GlobalTheory.CompanionTheory.HeckeSub
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportInducedFunctionClosed
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem isClosed_support_smooth_ind {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {W₁ : Type}
    [AddCommGroup W₁] [Module ℂ W₁] {Q : Subgroup G} (σ : Representation ℂ Q W₁) (f : smoothPart (ind Q σ)) :
    IsClosed {g : G | f.1.1 g ≠ 0} := by
  have hT : IsOpen {g : G | ind Q σ g f.1 = f.1} := f.2
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro g hg
  have hg0 : f.1.1 g = 0 := by simpa using hg
  have hc : Continuous fun h : G => g⁻¹ * h := continuous_const.mul continuous_id
  have hm : {h : G | g⁻¹ * h ∈ {κ : G | ind Q σ κ f.1 = f.1}} ∈ 𝓝 g :=
    (hT.preimage hc).mem_nhds (by
      show ind Q σ (g⁻¹ * g) f.1 = f.1
      simp)
  filter_upwards [hm] with h hh
  have e : (ind Q σ (g⁻¹ * h) f.1).1 g = f.1.1 g := congrArg (fun F : indSpace Q σ => F.1 g) hh
  have e' : f.1.1 (g * (g⁻¹ * h)) = f.1.1 g := e
  rw [mul_inv_cancel_left] at e'
  simpa [e', hg0] using hg0

end GlobalTheory.CompanionTheory.BZRes
end

