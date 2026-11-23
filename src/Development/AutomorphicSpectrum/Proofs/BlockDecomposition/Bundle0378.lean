module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0303
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0313
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0276
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisRight
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem mapH_id_bij {K : Type} [Field K] (C : Cx.{1} K) (n : ℕ) :
    Function.Bijective ((Cx.Hom.id C).mapH n) := by
  have h : ∀ x : C.H n, (Cx.Hom.id C).mapH n x = x := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  exact ⟨fun x y e => by simpa only [h] using e, fun y => ⟨y, h y⟩⟩

theorem swapPr_swapPr_apply {K : Type} [Field K] {P Q T : ℕ → Cx.{1} K}
    (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) {a a' c : ℕ} (ha : a + a' = c)
    {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j) :
    (swapPr (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) ha).μ h x y = (pr ha).μ h x y := by
  simp only [swapPr, LinearMap.smul_apply, LinearMap.flip_apply, smul_smul]
  have s : ((-1 : ℤ) ^ (i * j) * (-1) ^ (j * i)) = 1 := by
    rw [mul_comm j i, ← mul_pow]
    simp
  rw [s, one_smul]

theorem glue_l : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₂ : ObjectProperty E.C₂) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₁) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → U₂ (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun (capU V S) U₂ (capU W S) (h₁ S) (h₂ S)) → E.Kun (capU V ∅) U₂ (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  intro hMV hCD K _ E U₂ ι _ _ V W hV hW h₁ h₂ hK
  let Rel : ObjectProperty E.C₁ → ObjectProperty E.D → Prop := fun U U' =>
    (∀ T, U' T → U (E.L₁.obj T)) ∧ (∀ T, U' T → U₂ (E.L₂.obj T))
  let prr : ∀ (U : ObjectProperty E.C₁) (U' : ObjectProperty E.D), Rel U U' → ∀ {a a' c : ℕ}, a + a' = c →
      CxPairing (CH.cx (U₂.ι ⋙ E.F₂ a)) (CH.cx (U.ι ⋙ E.F₁ a')) (CH.cx (U'.ι ⋙ E.F₃ c)) :=
    fun U U' r {a a' c} ha =>
      swapPr (P := fun a => CH.cx (U.ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a))
        (T := fun c => CH.cx (U'.ι ⋙ E.F₃ c)) (fun {a a' c} ha => E.pr U U₂ U' r.1 r.2 ha) ha
  have hnat : ∀ {U₁ U₂' : ObjectProperty E.C₁} {U₁' U₂'' : ObjectProperty E.D} (r₁ : Rel U₁ U₁') (r₂ : Rel U₂' U₂'')
      (k : U₂' ≤ U₁) (k' : U₂'' ≤ U₁') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n)
      (x : (CH.cx (U₂.ι ⋙ E.F₂ a)).X i) (y : CH.Cn (U₁.ι ⋙ E.F₁ a') j),
      (resU (E.F₃ c) k').pullC n ((prr U₁ U₁' r₁ ha).μ hn x y) = (prr U₂' U₂'' r₂ ha).μ hn x ((resU (E.F₁ a') k).pullC j y) := by
    intro U₁ U₂' U₁' U₂'' r₁ r₂ k k' a a' c ha i j n hn x y
    simp only [prr, swapPr, LinearMap.smul_apply, LinearMap.flip_apply, map_zsmul]
    rw [_root_.GlobalTheory.CompanionTheory.KunGlue.pr_res E r₁.1 r₁.2 r₂.1 r₂.2 k (le_refl U₂) k' (show a' + a = c by omega) (show j + i = n by omega) y x,
      _root_.GlobalTheory.CompanionTheory.KunGlue.resU_self_pullC (E.F₂ a) U₂ (le_refl U₂) i x]
  have key := GlobalTheory.T.cosieve_pairing_family_compat hMV hCD E.F₁ E.F₃ (fun a => CH.cx (U₂.ι ⋙ E.F₂ a)) Rel prr hnat V W hV hW
    (fun S => ⟨h₁ S, h₂ S⟩) (fun S hS => GlobalTheory.T.kuenneth_swap _ (hK S hS))
  have k2 := GlobalTheory.T.kuenneth_swap _ key
  refine (_root_.GlobalTheory.CompanionTheory.KunGlue.Transfer.kunE_iff _ _ (fun a => Cx.Hom.id _) (fun a => Cx.Hom.id _) (fun a => Cx.Hom.id _)
    (fun a n => mapH_id_bij _ n) (fun a n => mapH_id_bij _ n) (fun a n => mapH_id_bij _ n) ?_).1 k2
  intro a a' c ha i j n h x y
  exact swapPr_swapPr_apply (P := fun a => CH.cx ((capU V ∅).ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a))
    (T := fun c => CH.cx ((capU W ∅).ι ⋙ E.F₃ c)) (fun {a a' c} ha => E.pr (capU V ∅) U₂ (capU W ∅) (h₁ ∅) (h₂ ∅) ha) ha h x y

end GlobalTheory.CompanionTheory.KunGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockHomeomorph
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.LeviIso

theorem leviEquiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∃ φ : Levi k m ≃* levi k N β, (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) ∧ Continuous φ ∧ Continuous φ.symm := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ
  have hz : ∀ x : GL (Fin N) k, x ∈ levi k N β → ∀ i j : Fin N, blk e i ≠ blk e j →
      (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
    intro x hx i j hij
    simp only [levi, Subgroup.mem_inf, GroundTheory.Automorphic.Iwasawa.mem_blockUpper] at hx
    rcases lt_or_gt_of_ne hij with h | h
    · exact hx.2 (OrderDual.toDual_lt_toDual.mpr ((hβ i j).2 h))
    · exact hx.1 ((hβ j i).2 h)
  have hzE : ∀ (g : Levi k m) (i j : Fin N), blk e i ≠ blk e j →
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0 := by
    intro g i j hij
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    have hab : a ≠ b := by simpa [blk] using hij
    exact leviEmb_apply_ne k e g hab i' j'
  have hent : ∀ (g : Levi k m) (a : α) (i j : m a),
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
        ((g a : GL (m a) k) : Matrix (m a) (m a) k) i j := by
    intro g a i j
    exact leviEmb_apply_same k e g a i j
  have hmem : ∀ g : Levi k m, leviEmb k e g ∈ levi k N β := by
    intro g
    simp only [levi, Subgroup.mem_inf, GroundTheory.Automorphic.Iwasawa.mem_blockUpper]
    constructor
    · intro i j h
      exact hzE g i j ((hβ j i).1 h).ne'
    · intro i j h
      exact hzE g i j ((hβ i j).1 (OrderDual.toDual_lt_toDual.1 h)).ne
  have hkey : ∀ x : GL (Fin N) k, x ∈ levi k N β →
      Matrix.blockDiagonal' (Matrix.blockDiag' ((x : Matrix (Fin N) (Fin N) k).submatrix e e)) =
        (x : Matrix (Fin N) (Fin N) k).submatrix e e := by
    intro x hx
    ext ⟨a, i⟩ ⟨b, j⟩
    by_cases hab : a = b
    · subst hab
      rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiag'_apply]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hab, Matrix.submatrix_apply,
        hz x hx _ _ (by simpa [blk] using hab)]
  have hmul : ∀ x y : GL (Fin N) k, x ∈ levi k N β → y ∈ levi k N β → ∀ a : α,
      Matrix.blockDiag' ((x : Matrix (Fin N) (Fin N) k).submatrix e e) a *
          Matrix.blockDiag' ((y : Matrix (Fin N) (Fin N) k).submatrix e e) a =
        Matrix.blockDiag' (((x * y : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a := by
    intro x y hx hy a
    rw [Units.val_mul, ← Matrix.submatrix_mul_equiv (x : Matrix (Fin N) (Fin N) k)
      (y : Matrix (Fin N) (Fin N) k) e e e, ← hkey x hx, ← hkey y hy]
    simp only [← Matrix.blockDiagonal'_mul, Matrix.blockDiag'_blockDiagonal']
  have hcont : ∀ f : Levi k m → Levi k m,
      (∀ a, Continuous fun g => ((f g a : GL (m a) k) : Matrix (m a) (m a) k)) →
        Continuous fun g => ((leviEmb k e (f g) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := by
    intro f hf
    refine continuous_matrix fun i j => ?_
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      simp only [hent]
      exact (hf a).matrix_elem i' j'
    · have h0 : ∀ g, ((leviEmb k e (f g) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
          (e ⟨a, i'⟩) (e ⟨b, j'⟩) = 0 := fun g => hzE _ _ _ (by simpa [blk] using hab)
      simp only [h0]
      exact continuous_const
  have hLE : Continuous (leviEmb k e) := continuous_leviEmb k e
  let ψ : levi k N β → Levi k m := fun x => (fun a =>
      ⟨Matrix.blockDiag' (((x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a,
        Matrix.blockDiag' ((((x : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a,
        by rw [hmul _ _ x.2 (inv_mem x.2), mul_inv_cancel, Units.val_one,
          Matrix.submatrix_one_equiv, Matrix.blockDiag'_one]; rfl,
        by rw [hmul _ _ (inv_mem x.2) x.2, inv_mul_cancel, Units.val_one,
          Matrix.submatrix_one_equiv, Matrix.blockDiag'_one]; rfl⟩ : ∀ a, GL (m a) k)
  refine ⟨{
      toFun := fun g => ⟨leviEmb k e g, hmem g⟩
      invFun := ψ
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }, fun g => rfl, ?_, ?_⟩
  · intro g
    refine funext fun a => ?_
    apply Units.ext
    ext i j
    simp only [ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
    exact hent g a i j
  · intro x
    apply Subtype.ext
    apply Units.ext
    ext i j
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      dsimp only
      rw [hent]
      simp only [ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
    · have h' : blk e (e ⟨a, i'⟩) ≠ blk e (e ⟨b, j'⟩) := by simpa [blk] using hab
      dsimp only
      rw [hzE _ _ _ h', hz _ x.2 _ _ h']
  · intro g h
    apply Subtype.ext
    exact map_mul (leviEmb k e) g h
  · exact hLE.subtype_mk hmem
  · change Continuous ψ
    refine continuous_pi fun a => ?_
    rw [Units.continuous_iff]
    constructor
    · refine continuous_matrix fun i j => ?_
      simp only [Function.comp_apply, ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
      exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
    · refine continuous_matrix fun i j => ?_
      simp only [ψ, Units.inv_mk, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
      exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem _ _

end GlobalTheory.CompanionTheory.LeviIso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LftMulRgt
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DiracK

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι]

def lft (ι : Type) [Fintype ι] [DecidableEq ι] : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (ι → V) where
  toFun T :=
    { toFun := fun x i => T (x i)
      map_add' := fun x y => by funext i; simp
      map_smul' := fun s x => by funext i; simp }
  map_one' := by ext x i; simp
  map_mul' S T := by ext x i; simp
  map_zero' := by ext x i; simp
  map_add' S T := by ext x i; simp
  commutes' s := by ext x i; simp [Module.algebraMap_end_apply]

def rgt (V : Type) [AddCommGroup V] [Module ℂ V] : Matrix ι ι ℂ →ₐ[ℂ] Module.End ℂ (ι → V) where
  toFun M :=
    { toFun := fun x i => ∑ j, M i j • x j
      map_add' := fun x y => by funext i; simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun s x => by
        funext i
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _ }
  map_one' := by
    ext x i
    simp [Matrix.one_apply]
  map_mul' M N := by
    apply LinearMap.ext
    intro x
    funext i
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum,
      smul_smul]
    exact Finset.sum_comm
  map_zero' := by ext x i; simp
  map_add' M N := by
    apply LinearMap.ext
    intro x
    funext i
    simp [add_smul, Finset.sum_add_distrib]
  commutes' s := by
    apply LinearMap.ext
    intro x
    funext i
    simp [Module.algebraMap_end_apply, Matrix.algebraMap_matrix_apply, ite_smul]

theorem lft_apply (T : Module.End ℂ V) (x : ι → V) (i : ι) : lft ι T x i = T (x i) := rfl

theorem rgt_apply (M : Matrix ι ι ℂ) (x : ι → V) (i : ι) : rgt V M x i = ∑ j, M i j • x j := rfl

theorem lft_mul_rgt (T : Module.End ℂ V) (M : Matrix ι ι ℂ) : lft ι T * rgt V M = rgt V M * lft ι T := by
  apply LinearMap.ext
  intro x
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lft_apply, rgt_apply, map_sum]

theorem yF_eq (Kf : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) :
    yF Kf c a b = lft ι (Kf a b) + rgt V (spinM c a b) := rfl

def dirac (P : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix ι ι ℂ) : Module.End ℂ (ι → V) :=
  ∑ a, ∑ b, lft ι (P a b) * rgt V (c b a)

end GlobalTheory.CompanionTheory.DiracK
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearRecurrenceGrowthBound
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.LinRec

lemma eq_zero_of_natDegree_eq_zero {p : ℂ[X]} (hp : p.Monic) (hd : p.natDegree = 0)
    {u : ℕ → ℂ} (hu : aeval shift p u = 0) : u = 0 := by
  have hp1 : p = 1 := by
    have h1 : p.coeff 0 = 1 := by
      have h2 := hp.coeff_natDegree
      rwa [hd] at h2
    rw [eq_C_of_natDegree_eq_zero hd, h1, C_1]
  subst hp1
  simpa using hu

theorem uniform_aeval (D : ℕ) (κ' κ : ℝ) (hκ : κ' < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℂ[X], p.Monic → p.natDegree ≤ D →
      (∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp κ') → ∀ (u : ℕ → ℂ) (M : ℝ), aeval shift p u = 0 →
      (∀ j < p.natDegree, ‖u j‖ ≤ M) → 0 ≤ M →
      ∀ i : ℕ, ‖u i‖ ≤ C * Real.exp (κ * i) * M := by
  have hδ : 0 < Real.exp κ - Real.exp κ' := sub_pos.2 (Real.exp_lt_exp.2 hκ)
  induction D with
  | zero =>
    refine ⟨0, le_rfl, fun p hp hd _ u M hu _ _ i => ?_⟩
    have hu0 := eq_zero_of_natDegree_eq_zero hp (Nat.le_zero.1 hd) hu
    simp [hu0]
  | succ D ih =>
    obtain ⟨C', hC', hB⟩ := ih
    have hE' : 0 < Real.exp κ' := Real.exp_pos _
    have hc : 0 ≤ C' * (1 + Real.exp κ') := by positivity
    have hC0 : 0 ≤ 1 + C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ') := by positivity
    refine ⟨_, hC0, fun p hp hd hr u M hu hM hM0 i => ?_⟩
    by_cases hd0 : p.natDegree = 0
    · have hu0 := eq_zero_of_natDegree_eq_zero hp hd0 hu
      have : 0 ≤ (1 + C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ')) *
          Real.exp (κ * i) * M := by positivity
      simpa [hu0] using this
    obtain ⟨z, hz⟩ : ∃ z, p.IsRoot z := IsAlgClosed.exists_root p (by
      intro h0
      exact hd0 (natDegree_eq_zero_iff_degree_le_zero.2 h0.le))
    have hzle := hr z hz
    have hzlt : ‖z‖ < Real.exp κ := hzle.trans_lt (Real.exp_lt_exp.2 hκ)
    obtain ⟨q, rfl⟩ := dvd_iff_isRoot.2 hz
    have hq : q.Monic := (monic_X_sub_C z).of_mul_monic_left hp
    have hqd : ((X - C z) * q).natDegree = q.natDegree + 1 := by
      rw [(monic_X_sub_C z).natDegree_mul hq, natDegree_X_sub_C]
      omega
    have hv : ∀ i : ℕ, ‖u (i + 1) - z * u i‖ ≤
        C' * (1 + Real.exp κ') * Real.exp (κ * i) * M := by
      intro i
      have hb := hB q hq (by omega)
        (fun w hw => hr w (by
          have hw' : eval w q = 0 := hw
          simp [IsRoot, hw']))
        (fun i => u (i + 1) - z * u i) ((1 + Real.exp κ') * M) (aeval_diff q z u hu)
        (fun j hj => ?_) (by positivity) i
      · calc ‖u (i + 1) - z * u i‖ ≤ C' * Real.exp (κ * i) * ((1 + Real.exp κ') * M) := hb
          _ = _ := by ring
      · calc ‖u (j + 1) - z * u j‖ ≤ ‖u (j + 1)‖ + ‖z * u j‖ := norm_sub_le _ _
          _ = ‖u (j + 1)‖ + ‖z‖ * ‖u j‖ := by rw [norm_mul]
          _ ≤ M + Real.exp κ' * M := add_le_add (hM _ (by omega))
              (mul_le_mul hzle (hM _ (by omega)) (norm_nonneg _) hE'.le)
          _ = _ := by ring
    have hg := geom_step z κ _ M hzlt hc hM0 u (hM 0 (by omega)) hv i
    refine hg.trans ?_
    have hdiv : C' * (1 + Real.exp κ') / (Real.exp κ - ‖z‖) ≤
        C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ') :=
      div_le_div_of_nonneg_left hc hδ (by linarith)
    have hEM : 0 ≤ Real.exp (κ * i) * M := by positivity
    calc _ = (1 + C' * (1 + Real.exp κ') / (Real.exp κ - ‖z‖)) * (Real.exp (κ * i) * M) := by ring
      _ ≤ (1 + C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ')) * (Real.exp (κ * i) * M) :=
        mul_le_mul_of_nonneg_right (by linarith) hEM
      _ = _ := by ring

theorem uniformRecBound :
    ∀ (D : ℕ) (κ' κ : ℝ), κ' < κ → ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℂ[X], p.Monic → p.natDegree ≤ D →
  (∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp κ') → ∀ (u : ℕ → ℂ) (M : ℝ),
  (∀ i, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * u (i + j) = 0) → (∀ j < p.natDegree, ‖u j‖ ≤ M) → 0 ≤ M →
  ∀ i : ℕ, ‖u i‖ ≤ C * Real.exp (κ * i) * M := by
  intro D κ' κ hκ
  obtain ⟨C, hC, h⟩ := uniform_aeval D κ' κ hκ
  refine ⟨C, hC, fun p hp hd hr u M hu hM hM0 i => h p hp hd hr u M ?_ hM hM0 i⟩
  funext i
  rw [aeval_shift]
  exact hu i

end GlobalTheory.CompanionTheory.LinRec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterFiniteExtension
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.HeckeChar

theorem exists_unit_model : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (μ : G E Ω →* (Qbar l)ˣ), Continuous μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
    ∃ (LL' : FinExt l) (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ), Bw.LL.1 ≤ LL'.1 ∧
      IsModel Bw ((rk1 μ).comp (Dec (F := E) A).subtype) LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) ∧
      (∀ g, ((ψ g : ↥LL'.1) : Qbar l) = ((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l)) ∧
      Continuous (fun g => ((ψ g : ↥LL'.1) : Qbar l)) ∧ ∀ g, ‖((ψ g : ↥LL'.1) : Qbar l)‖ = 1 := by
  intro E Ω _ _ _ _ _ l _ μ hμ w A _ O _ _ _ Bw
  have hc : Continuous fun g : G E Ω => ((μ g : (Qbar l)ˣ) : Qbar l) := Units.continuous_val.comp hμ
  have hent : ∀ (g : G E Ω) (i j : Fin 1),
      ((rk1 μ g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) i j = ((μ g : (Qbar l)ˣ) : Qbar l) := by
    intro g i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp [rk1]
  have hr : Continuous (fun g : G E Ω => ((rk1 μ g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l))) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact hc.congr fun g => (hent g i j).symm
  obtain ⟨L, hle, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) 1 (rk1 μ) hr Bw.LL
  have hmem : ∀ g : G E Ω, ((μ g : (Qbar l)ˣ) : Qbar l) ∈ L.1 := fun g => by
    have h := hL g 0 0
    rwa [hent] at h
  let ψ : ↥(Dec (F := E) A) →* (↥L.1)ˣ :=
    { toFun := fun g =>
        ⟨⟨((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l), hmem _⟩,
          ⟨((μ ((g : G E Ω)⁻¹) : (Qbar l)ˣ) : Qbar l), hmem _⟩,
          Subtype.ext (by simp [← Units.val_mul, ← map_mul]),
          Subtype.ext (by simp [← Units.val_mul, ← map_mul])⟩
      map_one' := Units.ext (Subtype.ext (by simp))
      map_mul' := fun g h => Units.ext (Subtype.ext (by simp)) }
  have hψ : ∀ g, ((ψ g : ↥L.1) : Qbar l) = ((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l) := fun g => rfl
  refine ⟨L, ψ, hle, ⟨hle, ?_⟩, hψ, ?_, fun g => ?_⟩
  · refine MonoidHom.ext fun g => Units.ext ?_
    ext i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp [Formalism.MainNotions.N.mapRep, PositivityTheory.HodgeLocalCharacter.HLC.toGL1, rk1, hψ]
  · exact hc.comp continuous_subtype_val
  · exact GlobalTheory.ExpFrame.CharUnit.norm_eq_one_of_compact μ hc _

end GlobalTheory.CompanionTheory.HeckeChar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProdEquivStandardBlocks
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenMultiProd

theorem multiProd_equiv_stdBlocks : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (e : (Σ a, Fin (d a)) ≃ Fin N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), Nonempty ((multiProd e π).Equiv (multiProd (stdBlocks d hd) π)) := by
  intro k _ _ _ _ h N d hd e X _ _ π
  exact (GlobalTheory.SmGL.Placing.parInd_jac_placing k (Fin h) (Fin N) (fun a => Fin (d a)) e (stdBlocks d hd) _).1 _

end GlobalTheory.CompanionTheory.GenMultiProd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RangeStable
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCount.KHw

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)

variable {n : ℕ}

section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {Kf : Fin n → Fin n → Module.End ℂ V}

theorem glRel_kF {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : IsPair E1 E2) : Formalism.REAL.GlRel (kF E1 E2) := by
  intro a b c d
  have h1 := h.gl1 a b c d
  have h2 := h.gl2 a b c d
  have c1 := h.comm a b c d
  have c2 := h.comm c d a b
  have key : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [kF, add_mul, mul_add, c1, ← c2]
    abel
  rw [key, h1, h2]
  simp only [kF]
  split_ifs <;> abel

end

end GlobalTheory.CompanionTheory.RealCount.KHw
end
end

