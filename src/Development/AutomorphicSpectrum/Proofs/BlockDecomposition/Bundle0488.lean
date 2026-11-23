module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0473
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriUnipotentDatum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0211
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0209

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerWhitCharReflect
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.PRep.WhitExact

theorem twKer_whitChar_reflect : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth π → IsSmooth σ → ∀ f : V →ₗ[ℂ] W, Function.Injective f → (∀ g v, f (π g v) = σ g (f v)) → ∀ v : V, f v ∈ twKer σ (unipB k (Fin N)) (whitChar ψ N) → v ∈ twKer π (unipB k (Fin N)) (whitChar ψ N) := by
  intro k _ _ _ _ ψ hψ N V W _ _ _ _ π σ hπ hσ f hf hfg v hv
  exact GlobalTheory.CompanionTheory.PRep.JacExact.twKer_reflect π σ hπ hσ _ _
    (GlobalTheory.Whittaker.isSmoothChar_whitChar hψ)
    (fun s hs => GlobalTheory.CompanionTheory.UnipExhaust.exists_compact_subgroup_of_finset k N s hs) f hf hfg v hv

end GlobalTheory.CompanionTheory.PRep.WhitExact
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne
section
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def rowOf (C : Matrix (Fin n) (Fin r) E) (i : Fin r) : Fin n → E := (cT (σ : E →+* E) C * J) i

def lineProj (C D : Matrix (Fin n) (Fin r) E) (i : Fin r) : Matrix (Fin n) (Fin n) E :=
  Matrix.vecMulVec (fun k => C k i) (rowOf σ J D i)

def projFam (X Y : Matrix (Fin n) (Fin r) E) : Fin r ⊕ Fin r → Matrix (Fin n) (Fin n) E :=
  Sum.elim (lineProj σ J X Y) (lineProj σ J Y X)

def anisoProj (X Y : Matrix (Fin n) (Fin r) E) : Matrix (Fin n) (Fin n) E :=
  1 - ∑ k, projFam σ J X Y k

def normMat (l : Fin n → E) : Matrix (Fin n) (Fin n) E := Matrix.vecMulVec (fun k => σ (l k)) l

def hermFam (X Y : Matrix (Fin n) (Fin r) E) : Option (Fin r ⊕ Fin r) → Matrix (Fin n) (Fin n) E
  | none => cT (σ : E →+* E) (anisoProj σ J X Y) * J * anisoProj σ J X Y
  | some (Sum.inl i) => normMat σ (rowOf σ J Y i)
  | some (Sum.inr i) => normMat σ (rowOf σ J X i)

variable {σ J} {X Y : Matrix (Fin n) (Fin r) E}

theorem leviMin_subset (X Y : Matrix (Fin n) (Fin r) E) : leviMin σ J X Y ⊆ minPar σ J X :=
  fun _ ⟨d, _, e, _⟩ => ⟨_, Matrix.blockTriangular_diagonal _, e⟩

theorem unipMin_subset_minParOne (X : Matrix (Fin n) (Fin r) E) : unipMin σ J X ⊆ minParOne σ J X := by
  rintro u ⟨B, hB, h1, e, -⟩
  exact ⟨B, hB, e, fun i => ⟨1, by rw [h1]; rfl, map_one _⟩⟩

theorem minParOne_props (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    IsClosed (minParOne σ J X) ∧ ∀ p ∈ minParOne σ J X, ∀ q ∈ minParOne σ J X, p * q ∈ minParOne σ J X := by
  obtain ⟨a, ha⟩ := exists_isTorus h hJ hW
  obtain ⟨τ, hc, hm, -, h0, h1⟩ := exists_tau h hJ hW ha
  have ha0 : a 0 = 1 := by
    have e := ha.add 0 0
    rw [add_zero] at e
    exact mul_left_cancel (e.symm.trans (mul_one _).symm)
  have key : ∀ p : minParSub X h hJ hW, p.1 ∈ minParOne σ J X ↔ τ p = 0 := fun p => by
    refine ⟨fun hp => h0 p.1 hp, fun hp => ?_⟩
    have := h1 p
    rwa [hp, ha0, inv_one, mul_one] at this
  constructor
  · have hcl : IsClosed (minPar σ J X) := isClosed_minPar h hJ hW
    have e : minParOne σ J X = Subtype.val '' (τ ⁻¹' {0}) := by
      ext p
      constructor
      · intro hp
        exact ⟨⟨p, minParOne_subset hp⟩, (key _).1 hp, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact (key q).2 hq
    rw [e]
    exact (hcl.isClosedEmbedding_subtypeVal.isClosedMap) _ (isClosed_singleton.preimage hc)
  · intro p hp q hq
    have := (key (⟨p, minParOne_subset hp⟩ * ⟨q, minParOne_subset hq⟩)).2 (by
      rw [hm, (key _).1 hp, (key _).1 hq, add_zero])
    exact this

end GlobalTheory.CompanionTheory.ParCocompact

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentFrameLevelTriangularStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_frame_level_triangular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (s : Fin r) (m : GAd σ J), m ∈ unipRad σ J (pre X s) → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (α β : FrameIx r), frameLev s α ≤ frameLev s β → (frameIdem (σ : E →+* E) J X Y α).map τ.1 * (archMat σ J τ (projArch σ J w m) - 1) * (frameIdem (σ : E →+* E) J X Y β).map τ.1 = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.frameIdem_mul_unipRad_mul_frameIdem | exact GlobalTheory.CompanionTheory.RapidDecay.frameIdem_mul_unipRad_mul_frameIdem | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.frameIdem_mul_unipRad_mul_frameIdem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEquivariantForm
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.EqForm

section LinAlg

theorem exists_form_of_faithful {k Q : Type} [Field k] [AddCommGroup Q] [Module k Q] [FiniteDimensional k Q]
    (R : Type) [CommRing R] [Algebra k R] [Module R Q] [IsScalarTower k R Q]
    (hf : ∀ r : R, (∀ x : Q, r • x = 0) → r = 0) (q₀ : Q) (h0 : q₀ ≠ 0) :
    ∃ μ : Module.Dual k Q, μ ≠ 0 ∧ ∀ (r : R) (c : k), r • q₀ = c • q₀ → ∀ x, μ (r • x) = c * μ x := by
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R Q q₀)
  have hI : ∀ r : R, r ∈ I ↔ r • q₀ = 0 := fun r => by simp [I, LinearMap.mem_ker]
  haveI : Module.Finite R Q := Module.Finite.of_restrictScalars_finite k R Q
  have hne : I • (⊤ : Submodule R Q) ≠ ⊤ := by
    intro htop
    obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I (⊤ : Submodule R Q)
      Module.Finite.fg_top (by rw [htop])
    have hr0 : r = 0 := hf r fun x => hr2 x trivial
    rw [hr0, zero_sub, hI] at hr1
    apply h0
    simpa using hr1
  let M : Submodule k Q := (I • (⊤ : Submodule R Q)).restrictScalars k
  have hM : M < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hne ?_
    apply Submodule.restrictScalars_injective k
    simpa [M] using h
  obtain ⟨μ, hμ0, hμ⟩ := Submodule.exists_le_ker_of_lt_top M hM
  refine ⟨μ, hμ0, fun r c hr x => ?_⟩
  have hmem : r - algebraMap k R c ∈ I := by
    rw [hI, sub_smul, hr, algebraMap_smul, sub_self]
  have hx : (r - algebraMap k R c) • x ∈ M := by
    have h2 : (r - algebraMap k R c) • x ∈ I • (⊤ : Submodule R Q) :=
      Submodule.smul_mem_smul hmem (Submodule.mem_top)
    exact (Submodule.restrictScalars_mem k _ _).2 h2
  have h1 : μ ((r - algebraMap k R c) • x) = 0 := hμ hx
  rw [sub_smul, algebraMap_smul, map_sub, μ.map_smul c x, smul_eq_mul, sub_eq_zero] at h1
  exact h1

theorem exists_eigenform_of_commute {Q : Type} [AddCommGroup Q] [Module ℂ Q] [FiniteDimensional ℂ Q] {ι : Type}
    (A : ι → Module.End ℂ Q) (hc : ∀ i j, Commute (A i) (A j))
    (ξ : ι → ℂ) (q₀ : Q) (h0 : q₀ ≠ 0) (hq : ∀ i, A i q₀ = ξ i • q₀) :
    ∃ μ : Module.Dual ℂ Q, μ ≠ 0 ∧ ∀ i x, μ (A i x) = ξ i * μ x := by
  have hcomm : ∀ a ∈ Set.range A, ∀ b ∈ Set.range A, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hc i j
  letI : IsMulCommutative (Algebra.adjoin ℂ (Set.range A)) :=
    Algebra.isMulCommutative_adjoin ℂ (fun a ha b hb _ => hcomm a ha b hb)
  letI : CommRing (Algebra.adjoin ℂ (Set.range A)) := by
    open scoped IsMulCommutative in exact inferInstance
  obtain ⟨μ, hμ0, hμ⟩ := exists_form_of_faithful (k := ℂ) (Q := Q) (Algebra.adjoin ℂ (Set.range A))
    (fun r hr => Subtype.ext (LinearMap.ext fun x => by
      change (r : Module.End ℂ Q) x = 0 at *
      exact hr x)) q₀ h0
  refine ⟨μ, hμ0, fun i x => ?_⟩
  exact hμ ⟨A i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ (ξ i) (hq i) x

end LinAlg

section Smooth

variable {Γ W : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup W] [Module ℂ W]

theorem mem_fixed_iff (ρ : Representation ℂ Γ W) (K : Subgroup Γ) (v : W) :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have h1 := h ⟨k, hk⟩
    simpa using h1
  · intro h k
    have h1 := h k k.2
    simpa using h1

theorem exists_eigenform_of_smooth [IsTopologicalGroup Γ] (ρ : Representation ℂ Γ W) (hρ : IsSmooth ρ)
    (K : Subgroup Γ) (hK : IsCompact (K : Set Γ)) (hcomm : ∀ a b : Γ, a * b = b * a)
    (hfin : FiniteDimensional ℂ (fixed ρ K)) (ξ : Γ → ℂ) (w₀ : W) (h0 : w₀ ≠ 0)
    (hw : ∀ t, ρ t w₀ = ξ t • w₀) (hξ : ∀ k ∈ K, ξ k = 1) :
    ∃ lam : Module.Dual ℂ W, lam ≠ 0 ∧ ∀ t w, lam (ρ t w) = ξ t * lam w := by
  have hst : ∀ t, ∀ v ∈ fixed ρ K, ρ t v ∈ fixed ρ K := by
    intro t v hv
    refine (mem_fixed_iff ρ K _).2 fun k hk => ?_
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply,
      (mem_fixed_iff ρ K v).1 hv k hk]
  let A : Γ → Module.End ℂ (fixed ρ K) := fun t => (ρ t).restrict (hst t)
  have hA : ∀ t (s : fixed ρ K), ((A t s : fixed ρ K) : W) = ρ t s := fun t s => rfl
  have hAc : ∀ a b, Commute (A a) (A b) := by
    intro a b
    refine LinearMap.ext fun s => Subtype.ext ?_
    show ρ a (ρ b s) = ρ b (ρ a s)
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
  have hw₀ : w₀ ∈ fixed ρ K := (mem_fixed_iff ρ K _).2 fun k hk => by rw [hw, hξ k hk, one_smul]
  obtain ⟨μ, hμ0, hμ⟩ := exists_eigenform_of_commute A hAc ξ ⟨w₀, hw₀⟩
    (fun h => h0 (congrArg Subtype.val h)) (fun t => Subtype.ext (hw t))
  have hnorm : ∀ t : Γ, t ∈ Subgroup.normalizer (K : Set Γ) := by
    intro t
    refine Subgroup.mem_normalizer_iff.2 fun h => ?_
    have e : t * h * t⁻¹ = h := by rw [hcomm t h, mul_inv_cancel_right]
    rw [e]
  have hE : ∀ t w, GlobalTheory.LocGL.idem hρ hK (ρ t w) = ρ t (GlobalTheory.LocGL.idem hρ hK w) := by
    intro t w
    have h1 : w - GlobalTheory.LocGL.idem hρ hK w ∈ twKer ρ K 1 := by
      rw [← GlobalTheory.LocGL.idem_eq_zero_iff hρ hK, map_sub,
        GlobalTheory.LocGL.idem_of_mem hρ hK (GlobalTheory.LocGL.idem_mem hρ hK w), sub_self]
    have h2 := twKer_le_comap ρ K t (hnorm t) h1
    rw [Submodule.mem_comap, ← GlobalTheory.LocGL.idem_eq_zero_iff hρ hK, map_sub, map_sub,
      GlobalTheory.LocGL.idem_of_mem hρ hK (hst t _ (GlobalTheory.LocGL.idem_mem hρ hK w)), sub_eq_zero] at h2
    exact h2
  let e : W →ₗ[ℂ] fixed ρ K := (GlobalTheory.LocGL.idem hρ hK).codRestrict _ (GlobalTheory.LocGL.idem_mem hρ hK)
  refine ⟨μ ∘ₗ e, ?_, ?_⟩
  · intro h
    apply hμ0
    refine LinearMap.ext fun s => ?_
    have h1 : e (s : W) = s := Subtype.ext (GlobalTheory.LocGL.idem_of_mem hρ hK s.2)
    have h2 := LinearMap.congr_fun h (s : W)
    simpa [h1] using h2
  · intro t w
    have h1 : e (ρ t w) = A t (e w) := Subtype.ext (hE t w)
    simp only [LinearMap.comp_apply]
    rw [h1, hμ]

end Smooth

section Diag

variable {L : Type} [Field L]

theorem isDiagM_commute {n : ℕ} {g h : GL (Fin n) L} (hg : IsDiagM g) (hh : IsDiagM h) : g * h = h * g := by
  have key : ∀ a : GL (Fin n) L, IsDiagM a →
      (a : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => (a : Matrix (Fin n) (Fin n) L) i i := by
    intro a ha
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [ha i j hij, Matrix.diagonal_apply_ne _ hij]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, key g hg, key h hh, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [mul_comm]

end Diag

theorem eqFormU_of (hA4 : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], A4 G)
    (hIw : IwahoriU) (hDom : DomU) (hKU : KUFacts) : EqFormU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ hu hadm ξ y hy hyt hyk
  obtain ⟨D, hJ, hN, hNm, hT⟩ := hIw L ϖ σ q hu n
  obtain ⟨-, -, hIK, t, htD, htS⟩ := hKU L ϖ σ q n hu
  have hdom : D.IsStrDom ⟨t, (hT t).2 htD⟩ := (hDom L ϖ σ q hu n D hJ hN hNm hT ⟨t, (hT t).2 htD⟩).2 htS
  have a4 := (hA4 (GU σ n) D V ρ hadm ⟨_, hdom⟩).2
  have hker : twKer ρ D.N 1 = jacU ρ := twKer_eq_jacSub D _ hN ρ
  haveI hfJ : FiniteDimensional ℂ (fixed ρ D.J) := hadm.2 D.J D.isOpen_J D.isCompact_J
  have hfin : FiniteDimensional ℂ (fixed (D.piN ρ) D.JT) := by
    let f : fixed ρ D.J →ₗ[ℂ] Jacquet ρ D.N := (twKer ρ D.N 1).mkQ ∘ₗ (fixed ρ D.J).subtype
    have hle : fixed (D.piN ρ) D.JT ≤ LinearMap.range f := by
      intro w hw
      obtain ⟨v, hv⟩ := a4 w hw
      exact ⟨v, hv⟩
    exact Submodule.finiteDimensional_of_le hle
  have hsm : IsSmooth (D.piN ρ) := by
    intro w
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    let Sg : Subgroup D.T :=
      { carrier := {g | D.piN ρ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have hop : IsOpen {g : D.T | ρ (g : GU σ n) v = v} := (hadm.1 v).preimage continuous_subtype_val
    refine Sg.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hop.mem_nhds (by simp)) ?_)
    intro g hg
    show D.piN ρ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v
    have hp : D.piN ρ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ (g : GU σ n) v) := rfl
    rw [hp, show ρ (g : GU σ n) v = v from hg]
  have hcpt : IsCompact (D.JT : Set D.T) := by
    rw [Subtype.isCompact_iff]
    have e : Subtype.val '' (D.JT : Set D.T) = (D.J : Set (GU σ n)) ∩ D.T := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨ha, a.2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨x, h2⟩, h1, rfl⟩
    rw [e]
    exact D.isCompact_J.inter_right D.isClosed_alt
  have hcomm : ∀ a b : D.T, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact isDiagM_commute ((hT _).1 a.2) ((hT _).1 b.2)
  have hmk : ∀ x : V, x ∈ jacU ρ ↔ (Submodule.Quotient.mk x : Jacquet ρ D.N) = 0 := by
    intro x
    rw [Submodule.Quotient.mk_eq_zero, hker]
  obtain ⟨lam₀, hlam0, hlam⟩ := exists_eigenform_of_smooth (D.piN ρ) hsm D.JT hcpt hcomm hfin
    (fun a => ξ (a : GU σ n)) (Submodule.Quotient.mk y) (fun h => hy ((hmk y).2 h))
    (fun a => by
      have hp : D.piN ρ a (Submodule.Quotient.mk y) = Submodule.Quotient.mk (ρ (a : GU σ n) y) := rfl
      rw [hp, ← Submodule.Quotient.mk_smul, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
      exact (hmk _).1 (hyt _ ((hT _).1 a.2)))
    (fun k hk => hyk _ (hIK (hJ ▸ hk)) ((hT _).1 k.2))
  refine ⟨lam₀ ∘ₗ (twKer ρ D.N 1).mkQ, ?_, ?_, ?_⟩
  · intro x hx
    have h1 : (twKer ρ D.N 1).mkQ x = 0 := (hmk x).1 hx
    simp [h1]
  · intro h
    apply hlam0
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact LinearMap.congr_fun h v
  · intro s hs v
    exact hlam ⟨s, (hT s).2 hs⟩ (Submodule.Quotient.mk v)

theorem eqFormU : EqFormU :=
  eqFormU_of (fun G _ _ _ => _root_.GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4 G) _root_.GlobalTheory.CompanionTheory.IwUnit.iwahoriU GlobalTheory.CompanionTheory.DomUnitary.domU GlobalTheory.CompanionTheory.KUFactsU.kuFacts

end GlobalTheory.CompanionTheory.EqForm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExponentialPathExists
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.KCurve

section
open scoped Matrix.Norms.L2Operator

theorem exists_exp_eq_of_unitary {n : ℕ} (k : Matrix (Fin n) (Fin n) ℂ)
    (hu : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp Y = k := by
  haveI : IsStarNormal k :=
    ⟨(Unitary.star_mul_self_of_mem hu).trans (Unitary.mul_star_self_of_mem hu).symm⟩
  have hfin := Matrix.finite_spectrum k
  have hunit : IsUnit k := (Unitary.toUnits ⟨k, hu⟩).isUnit
  have hne : ∀ x ∈ spectrum ℂ k, x ≠ 0 := fun x hx h0 =>
    (spectrum.zero_notMem_iff ℂ).mpr hunit (h0 ▸ hx)
  refine ⟨cfc Complex.log k, ?_⟩
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ) (p := IsStarNormal) (a := cfc Complex.log k),
    ← cfc_comp (R := ℂ) (p := IsStarNormal) NormedSpace.exp Complex.log k
      (hg := (hfin.image _).continuousOn _) (hf := hfin.continuousOn _)]
  have hc : cfc (NormedSpace.exp ∘ Complex.log) k = cfc (id : ℂ → ℂ) k := by
    refine cfc_congr fun x hx => ?_
    simp only [Function.comp, id]
    rw [← Complex.exp_eq_exp_ℂ, Complex.exp_log (hne x hx)]
  rw [hc, cfc_id ℂ k]

end

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def atPlace (w : InfinitePlace E) :
    Matrix (Fin a) (Fin a) (Cinf E) →+* Matrix (Fin a) (Fin a) ℂ :=
  (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix

theorem atPlace_apply (w : InfinitePlace E) (x : Matrix (Fin a) (Fin a) (Cinf E)) (i j : Fin a) :
    atPlace w x i j = x i j w := rfl

theorem continuous_atPlace (w : InfinitePlace E) :
    Continuous (atPlace (a := a) w) :=
  continuous_id.matrix_map (continuous_apply w)

theorem atPlace_star (w : InfinitePlace E) (x : Matrix (Fin a) (Fin a) (Cinf E)) :
    atPlace w (star x) = star (atPlace w x) := by
  ext i j
  rfl

theorem exists_exp_eq (k : Kinf E a) :
    ∃ M : Matrix (Fin a) (Fin a) (Cinf E), NormedSpace.exp M = k.1 := by
  have hk : ∀ w, atPlace w k.1 ∈ unitary (Matrix (Fin a) (Fin a) ℂ) := fun w =>
    Unitary.mem_iff.mpr
      ⟨by rw [← atPlace_star, ← map_mul, Unitary.star_mul_self_of_mem k.2, map_one],
       by rw [← atPlace_star, ← map_mul, Unitary.mul_star_self_of_mem k.2, map_one]⟩
  choose Y hY using fun w => exists_exp_eq_of_unitary (atPlace w k.1) (hk w)
  refine ⟨Matrix.of fun i j w => Y w i j, Matrix.ext fun i j => ?_⟩
  funext w
  have h1 := congrArg (fun m => m i j)
    (NormedSpace.map_exp (atPlace w) (continuous_atPlace w) (Matrix.of fun i j w => Y w i j))
  have hM : atPlace w (Matrix.of fun i j w => Y w i j) = Y w := by
    ext i' j'
    rfl
  simp only [atPlace_apply, hM] at h1
  exact h1.trans ((congrArg (fun m => m i j) (hY w)).trans (atPlace_apply w k.1 i j))

theorem exists_curve : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (k : Kinf E a), ∃ (c : ℝ → GL (Fin a) (Cinf E)) (Y : Lie E a), c 0 = 1 ∧ c 1 = Unitary.toUnits k ∧ (∀ s, HasDerivAt (fun t => toL (c t).val) (toL ((c s).val * Matrix.of Y)) s) ∧ (∀ s, HasDerivAt (fun t => toL ((c t)⁻¹).val) (toL (-(Matrix.of Y * ((c s)⁻¹).val))) s) := by
  intro E _ _ _ a k
  obtain ⟨M, hM⟩ := exists_exp_eq k
  have htoL : ∀ N : Matrix (Fin a) (Fin a) (Cinf E), toL N = GlobalTheory.CompanionTheory.LieCurve.toLieL E a N := fun N => by
    rw [GlobalTheory.CompanionTheory.LieCurve.toLieL_apply]
  have hof : Matrix.of (GlobalTheory.CompanionTheory.LieCurve.toLieL E a M) = M := by
    rw [GlobalTheory.CompanionTheory.LieCurve.toLieL_apply]
    rfl
  refine ⟨GlobalTheory.CompanionTheory.LieCurve.expUnit E a M, GlobalTheory.CompanionTheory.LieCurve.toLieL E a M,
    GlobalTheory.CompanionTheory.LieCurve.expUnit_zero E a M, ?_, fun s => ?_, fun s => ?_⟩
  · apply Units.ext
    rw [GlobalTheory.CompanionTheory.LieCurve.expUnit_val, one_smul, hM]
    rfl
  · simp only [GlobalTheory.CompanionTheory.LieCurve.expUnit_val, hof, htoL]
    exact (GlobalTheory.CompanionTheory.LieCurve.toLieL E a).hasFDerivAt.comp_hasDerivAt s
      (GlobalTheory.CompanionTheory.LieCurve.hasDerivAt_exp E a M s)
  · simp only [GlobalTheory.CompanionTheory.LieCurve.expUnit_inv_val, hof, htoL]
    have h1 := GlobalTheory.CompanionTheory.LieCurve.hasDerivAt_exp E a (-M) s
    have e1 : (fun t : ℝ => NormedSpace.exp (t • -M)) = fun t : ℝ => NormedSpace.exp (-t • M) := by
      funext t
      rw [neg_smul, smul_neg]
    have e2 : NormedSpace.exp (s • -M) * -M = -(M * NormedSpace.exp (-s • M)) := by
      rw [smul_neg, ← neg_smul, mul_neg, ((Commute.refl M).smul_right (-s)).exp_right.eq]
    rw [e1, e2] at h1
    exact (GlobalTheory.CompanionTheory.LieCurve.toLieL E a).hasFDerivAt.comp_hasDerivAt s h1

end GlobalTheory.CompanionTheory.SmoothRep.KCurve
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetEigenvectorExists
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.EigTorus

theorem eigU_complete :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ∀ y : V, y ∉ jacU ρ →
    (∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ρ k y - y ∈ jacU ρ) →
    ∃ (y' : V) (ξ : GU σ n → ℂ), y' ∉ jacU ρ ∧ (∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ρ t y' - ξ t • y' ∈ jacU ρ) ∧
      ∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ξ k = 1 :=
  eigU_of _root_.GlobalTheory.CompanionTheory.IwUnit.iwahoriU _root_.GlobalTheory.CompanionTheory.DomUnitary.domU GlobalTheory.CompanionTheory.KUFactsU.kuFacts (fun G _ _ _ => _root_.GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4 G)

end GlobalTheory.CompanionTheory.EigTorus
end

