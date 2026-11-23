module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0359
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.HighestWeightDifferencesNat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0335
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0356
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0361
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRepsSumEqZero
section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem coe_polyBall_eq (n : ℕ) (t : kˣ) :
    (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) =
      Multiplicative.ofAdd '' FourierPi.box (Fin n) t := by
  ext x
  constructor
  · intro hx
    exact ⟨x.toAdd, fun i _ => hx i, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact fun i => hy i trivial

theorem isCompact_polyBall (n : ℕ) (t : kˣ) :
    IsCompact (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) := by
  rw [coe_polyBall_eq]
  exact (FourierPi.isCompact_box t).image (continuous_ofAdd)

theorem isOpen_polyBall (n : ℕ) (t : kˣ) :
    IsOpen (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) := by
  have h : (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) =
      Multiplicative.toAdd ⁻¹' FourierPi.box (Fin n) t := by
    ext x
    exact ⟨fun hx i _ => hx i, fun hx i => hx i trivial⟩
  rw [h]
  exact (FourierPi.isOpen_box t).preimage continuous_toAdd

theorem dotProduct_mem_cball {n : ℕ} {a b c : kˣ} (h : valuation k (a : k) * valuation k (b : k) ≤ valuation k (c : k))
    {u x : Fin n → k} (hu : ∀ i, u i ∈ cball a) (hx : ∀ i, x i ∈ cball b) : u ⬝ᵥ x ∈ cball c := by
  refine Finset.sum_induction _ (· ∈ cball c) (fun _ _ => add_mem_cball) (by simp [cball]) fun i _ => ?_
  show valuation k (u i * x i) ≤ valuation k (c : k)
  rw [map_mul]
  exact (mul_le_mul' (hu i) (hx i)).trans h

theorem exists_reps_sum_eq_zero :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (t s : kˣ),
      ∃ R : Finset (Fin n → k), R.Nonempty ∧ (∀ a ∈ R, Multiplicative.ofAdd a ∈ polyBall n t) ∧
        ∀ x : polyBall (k := k) n s, (x : Multiplicative (Fin n → k)) ∉ ann ψ n t →
          ∑ a ∈ R, (((resChr ψ a (polyBall n s) x)⁻¹ : ℂˣ) : ℂ) = 0 := by
  intro k _ _ _ _ ψ hψ n t s
  classical
  obtain ⟨c, hc⟩ := exists_cball_addChar_eq_one ψ hψ
  obtain ⟨t', ht1, ht2⟩ : ∃ t' : kˣ, valuation k (t' : k) ≤ valuation k (t : k) ∧
      valuation k (t' : k) ≤ valuation k ((c * s⁻¹ : kˣ) : k) := by
    rcases le_total (valuation k (t : k)) (valuation k ((c * s⁻¹ : kˣ) : k)) with h | h
    · exact ⟨t, le_rfl, h⟩
    · exact ⟨c * s⁻¹, h, le_rfl⟩
  have hts : valuation k (t' : k) * valuation k (s : k) ≤ valuation k (c : k) := by
    have hs0 : valuation k (s : k) ≠ 0 := by simp
    calc valuation k (t' : k) * valuation k (s : k)
        ≤ valuation k ((c * s⁻¹ : kˣ) : k) * valuation k (s : k) := mul_le_mul_left ht2 _
      _ = valuation k (c : k) := by
        rw [← map_mul]
        simp
  let H : Subgroup (Multiplicative (Fin n → k)) := polyBall n t
  let N : Subgroup H := (polyBall n t').subgroupOf H
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp (isCompact_polyBall n t)
  have hNopen : IsOpen (N : Set H) := (isOpen_polyBall n t').preimage continuous_subtype_val
  haveI : Finite (H ⧸ N) := Subgroup.quotient_finite_of_isOpen _ hNopen
  letI : Fintype (H ⧸ N) := Fintype.ofFinite _
  haveI : N.Normal := ⟨fun a ha b => by
    rw [mul_comm b a, mul_inv_cancel_right]; exact ha⟩
  let rep : H ⧸ N → Fin n → k := fun q => ((q.out : H) : Multiplicative (Fin n → k)).toAdd
  have hinj : Function.Injective rep := fun p q h =>
    Quotient.out_injective (Subtype.ext (Multiplicative.toAdd.injective h))
  refine ⟨Finset.univ.image rep, ?_, ?_, ?_⟩
  · exact ⟨rep 1, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  · intro a ha
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    exact (q.out : H).2
  · intro x hx
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    obtain ⟨l₀, hl₀, hne⟩ : ∃ a ∈ polyBall (k := k) n t, ψ (a.toAdd ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd) ≠ 1 := by
      by_contra h
      push Not at h
      exact hx h
    let y : H → Circle := fun b => (ψ ((b : Multiplicative (Fin n → k)).toAdd ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd))⁻¹
    let f : H → ℂ := fun b => (y b : ℂ)
    have hmul : ∀ b b' : H, f (b * b') = f b * f b' := by
      intro b b'
      simp only [f, y, ← Circle.coe_mul]
      congr 1
      rw [Subgroup.coe_mul, toAdd_mul, add_dotProduct, AddChar.map_add_eq_mul, mul_inv]
    have hN : ∀ b, ∀ u ∈ N, f (b * u) = f b := by
      intro b u hu
      have h1 : ψ ((u : Multiplicative (Fin n → k)).toAdd ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd) = 1 :=
        hc _ (dotProduct_mem_cball hts (Subgroup.mem_subgroupOf.1 hu) x.2)
      have h2 : f u = 1 := by simp [f, y, h1]
      rw [hmul, h2, mul_one]
    let l : H := ⟨l₀, hl₀⟩
    have hl : f l ≠ 1 := by
      intro h
      apply hne
      have h3 : y l = 1 := Circle.ext (by simpa [f] using h)
      simpa [y, l] using h3
    have hsum := GlobalTheory.CompanionTheory.TwistedAverage.sum_out_mul_right N f hN l
    simp only [hmul] at hsum
    rw [← Finset.sum_mul] at hsum
    have hS : ∑ q : H ⧸ N, f q.out = 0 := by
      have h4 : (∑ q : H ⧸ N, f q.out) * (f l - 1) = 0 := by
        rw [mul_sub, hsum, mul_one, sub_self]
      exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hl)
    rw [← hS]
    refine Finset.sum_congr rfl fun q _ => ?_
    show (((Circle.toUnits (ψ (rep q ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd)))⁻¹ : ℂˣ) : ℂ) = f q.out
    simp [f, y, rep]

end GlobalTheory.CompanionTheory.MirFourier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalOfHom
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.HomTrace

theorem finiteDimensional_of_hom (W H : Type) [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] [Nontrivial W] [FiniteDimensional ℂ (W →ₗ[ℂ] H)] :
    FiniteDimensional ℂ H := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have hex : ∃ φ : Module.Dual ℂ W, φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).1 hcon)
  obtain ⟨φ, hφ⟩ := hex
  let j : H →ₗ[ℂ] (W →ₗ[ℂ] H) :=
    { toFun := fun h => φ.smulRight h
      map_add' := fun x y => by ext v; simp
      map_smul' := fun c x => by
        ext v
        simp only [LinearMap.smulRight_apply, LinearMap.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
  have hj : Function.Injective j := by
    intro x y hxy
    have h1 : φ w • x = φ w • y := by
      simpa [j] using LinearMap.congr_fun hxy w
    exact smul_right_injective H hφ h1
  exact FiniteDimensional.of_injective j hj

noncomputable def sandwich {W H : Type} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] (a : H →ₗ[ℂ] H) (b : W →ₗ[ℂ] W) :
    (W →ₗ[ℂ] H) →ₗ[ℂ] (W →ₗ[ℂ] H) where
  toFun f := a ∘ₗ f ∘ₗ b
  map_add' f g := by ext v; simp
  map_smul' c f := by ext v; simp

theorem trace_sandwich {W H : Type} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] [FiniteDimensional ℂ W] [FiniteDimensional ℂ H]
    (a : H →ₗ[ℂ] H) (b : W →ₗ[ℂ] W) :
    LinearMap.trace ℂ (W →ₗ[ℂ] H) (sandwich a b) =
      LinearMap.trace ℂ W b * LinearMap.trace ℂ H a := by
  let e := dualTensorHomEquiv ℂ W H
  let M : (TensorProduct ℂ (Module.Dual ℂ W) H) →ₗ[ℂ] (TensorProduct ℂ (Module.Dual ℂ W) H) :=
    TensorProduct.map (Module.Dual.transpose (R := ℂ) b) a
  have hcomp : (e : _ →ₗ[ℂ] _) ∘ₗ M = sandwich a b ∘ₗ (e : _ →ₗ[ℂ] _) := by
    apply TensorProduct.ext'
    intro φ h
    ext v
    simp [e, M, sandwich, dualTensorHomEquiv, dualTensorHomEquivOfBasis_apply, dualTensorHom_apply,
      Module.Dual.transpose_apply]
  have hconj : e.conj M = sandwich a b := by
    rw [LinearEquiv.conj_apply]
    ext1 f
    have := LinearMap.congr_fun hcomp (e.symm f)
    simpa using this
  rw [← hconj, LinearMap.trace_conj', LinearMap.trace_tensorProduct', LinearMap.trace_transpose']

end GlobalTheory.CompanionTheory.HomTrace
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedVectorZeroOfDual
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.CompactAvg

theorem invariant_forms_separate_fixed :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G),
      IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ G V), IsSmooth π → ∀ u ∈ fixed π J,
      (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l u = 0) → u = 0 := by
  intro G _ _ _ J hJ V _ _ π hπ u hu hl
  obtain ⟨E, -, hfix, -, hinv, -⟩ := _root_.GlobalTheory.CompanionTheory.CompactAvg.exists_average G J hJ V π hπ
  by_contra hne
  have hex : ∃ l0 : Module.Dual ℂ V, l0 u ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ u).1 hall)
  obtain ⟨l0, hl0⟩ := hex
  have hzero : (l0 ∘ₗ E) u = 0 := by
    refine hl (l0 ∘ₗ E) fun x hx => ?_
    rw [LinearMap.comp_assoc, hinv x hx]
  apply hl0
  simpa [hfix u hu] using hzero

end GlobalTheory.CompanionTheory.CompactAvg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProjectiveOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_existence_projective_open : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {N : ℕ} {Y : Scheme.{0}} (i : Y ⟶ projectiveSpace A N), IsClosedImmersion i → ∀ (O : Y.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ i ≫ ProjSpace.toSpecBase A N⟩; Statement I (⊥ : (O : Scheme.{0}).IdealSheafData) := by
  first | exact @GlobalTheory.CompanionTheory.GE.statement_open_projective | exact GlobalTheory.CompanionTheory.GE.statement_open_projective | (intros; apply GlobalTheory.CompanionTheory.GE.statement_open_projective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanLocal
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenGK

theorem gkLocal_gen : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k :=
  fun hA => GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA

end GlobalTheory.CompanionTheory.GenGK
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericHasGenericIrreducibleSubquotient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenExists

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_subQuot [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    (A B : Subrepresentation ρ) : IsSmooth (subQuot A B) := by
  have stab : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) (w : W),
      ∃ H : Subgroup G, ∀ g, g ∈ H ↔ σ g w = w := by
    intro W _ _ σ w
    refine ⟨{ carrier := {g | σ g w = w}, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun g => Iff.rfl⟩
    · intro a b ha hb
      replace ha : σ a w = w := ha
      replace hb : σ b w = w := hb
      show σ (a * b) w = w
      rw [map_mul, Module.End.mul_apply, hb, ha]
    · show σ 1 w = w
      rw [map_one, Module.End.one_apply]
    · intro a ha
      replace ha : σ a w = w := ha
      show σ a⁻¹ w = w
      conv_lhs => rw [← ha]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  intro v
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨H₁, hH₁⟩ := stab ρ (x : V)
  obtain ⟨H₂, hH₂⟩ := stab (subQuot A B) (Submodule.Quotient.mk x)
  have hle : H₁ ≤ H₂ := by
    intro g hg
    rw [hH₁] at hg
    rw [hH₂]
    show Submodule.Quotient.mk (A.toRepresentation g x) = Submodule.Quotient.mk x
    congr 1
    exact Subtype.ext hg
  have e₁ : (H₁ : Set G) = {g | ρ g x = x} := Set.ext hH₁
  have e₂ : (H₂ : Set G) = {g | (subQuot A B) g (Submodule.Quotient.mk x) = Submodule.Quotient.mk x} :=
    Set.ext hH₂
  rw [← e₂]
  exact Subgroup.isOpen_mono hle (e₁ ▸ hρ x)

theorem nontrivial_twJacquet_subQuot {ρ : Representation ℂ G V} (N : Subgroup G) (χ : N →* ℂˣ)
    (A B : Subrepresentation ρ) (hB : B.toSubmodule ≤ twKer ρ N χ) (hA : ¬ A.toSubmodule ≤ twKer ρ N χ) :
    Nontrivial (TwJacquet (subQuot A B) N χ) := by
  obtain ⟨a, haA, hak⟩ := SetLike.not_le_iff_exists.mp hA
  let φ : A.toSubmodule →ₗ[ℂ] V ⧸ twKer ρ N χ := (twKer ρ N χ).mkQ ∘ₗ A.toSubmodule.subtype
  have hφ : Submodule.comap A.toSubmodule.subtype B.toSubmodule ≤ LinearMap.ker φ := by
    intro x hx
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (x : V) = (0 : V ⧸ twKer ρ N χ)
    rw [Submodule.Quotient.mk_eq_zero]
    exact hB (Submodule.mem_comap.mp hx)
  let Ψ := (Submodule.comap A.toSubmodule.subtype B.toSubmodule).liftQ φ hφ
  have hker : twKer (subQuot A B) N χ ≤ LinearMap.ker Ψ := by
    apply Submodule.span_le.mpr
    rintro w ⟨n, v, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul]
    show Submodule.Quotient.mk (ρ n (x : V)) - (χ n : ℂ) • Submodule.Quotient.mk (x : V) =
      (0 : V ⧸ twKer ρ N χ)
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨n, (x : V), rfl⟩
  refine ⟨⟨(Submodule.Quotient.mk (Submodule.Quotient.mk ⟨a, haA⟩ :
      A.toSubmodule ⧸ Submodule.comap A.toSubmodule.subtype B.toSubmodule) :
      _ ⧸ twKer (subQuot A B) N χ), 0, ?_⟩⟩
  intro h
  rw [Submodule.Quotient.mk_eq_zero] at h
  have h' := hker h
  rw [LinearMap.mem_ker] at h'
  have h'' : Submodule.Quotient.mk a = (0 : V ⧸ twKer ρ N χ) := h'
  exact hak ((Submodule.Quotient.mk_eq_zero _).mp h'')

end General

theorem exists_generic_subQuot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → GlobalTheory.SmGL.HasFiniteLength ρ →
    IsGenericFor ψ ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ (subQuot A B).IsIrreducible ∧
      IsSmooth (subQuot A B) ∧ IsGenericFor ψ (subQuot A B) := by
  intro k _ _ _ _ ψ hψ N V _ _ ρ hρ hfl hgen
  have hNA := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  haveI := hNA.1
  haveI := hNA.2
  have hle : ∀ S T : Subrepresentation ρ, S.asSubmodule ≤ T.asSubmodule ↔ S ≤ T := fun S T => Iff.rfl
  have hsm : StrictMono (fun S : Subrepresentation ρ => S.asSubmodule) := fun S T h =>
    lt_of_le_of_ne ((hle S T).mpr h.le)
      (fun he => h.ne (le_antisymm ((hle S T).mp he.le) ((hle T S).mp he.ge)))
  have wfl : WellFounded (fun S T : Subrepresentation ρ => S < T) :=
    Subrelation.wf (fun {S T} h => hsm h) (InvImage.wf (fun S : Subrepresentation ρ => S.asSubmodule) wellFounded_lt)
  have wfg : WellFounded (fun S T : Subrepresentation ρ => T < S) :=
    Subrelation.wf (fun {S T} h => hsm h) (InvImage.wf (fun S : Subrepresentation ρ => S.asSubmodule) wellFounded_gt)
  have hgen' : Nontrivial (V ⧸ twKer ρ (unipB k (Fin N)) (whitChar ψ N)) := hgen
  let T0 : Subrepresentation ρ := ⟨⊤, fun _ _ _ => Submodule.mem_top⟩
  have htop : ¬ T0.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
    intro h
    obtain ⟨x, y, hxy⟩ := hgen'.exists_pair_ne
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    apply hxy
    rw [Submodule.Quotient.eq]
    exact h Submodule.mem_top
  obtain ⟨A, hAP, hAmin⟩ := wfl.has_min {A | ¬ A.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N)} ⟨T0, htop⟩
  let Z : Subrepresentation ρ := ⟨⊥, fun g v hv => by
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]⟩
  have hZk : Z.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := bot_le
  have hZA : Z < A := by
    refine lt_of_le_of_ne ?_ ?_
    · intro x hx
      have hx0 : x = 0 := (Submodule.mem_bot ℂ).mp hx
      rw [hx0]
      exact A.toSubmodule.zero_mem
    · intro h
      rw [← h] at hAP
      exact hAP hZk
  obtain ⟨B, hBA, hBmax⟩ := wfg.has_min {B | B < A} ⟨Z, hZA⟩
  have hcov : B ⋖ A := ⟨hBA, fun C hBC hCA => hBmax C hCA hBC⟩
  have hBk : B.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
    by_contra h
    exact hAmin B h hBA
  exact ⟨A, B, hBA.le, GlobalTheory.SmGL.isIrreducible_subQuot hcov, GlobalTheory.CompanionTheory.GenExists.isSmooth_subQuot hρ A B,
    GlobalTheory.CompanionTheory.GenExists.nontrivial_twJacquet_subQuot _ _ A B hBk hAP⟩

end GlobalTheory.CompanionTheory.GenExists

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightAntitoneOfFiniteDimensionalStable
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount

theorem highestWeight_antitone_of_finiteDimensional_stable :
    ∀ {n : ℕ} (V : Type) [AddCommGroup V] [Module ℂ V] (Kf : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V)
    (ν : Fin n → ℝ) (v : V), Formalism.REAL.GlRel Kf → FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, Kf a b w ∈ S) → v ∈ S → v ≠ 0 →
    Formalism.REAL.KHighest (fun _ => true) Kf ν v → Antitone ν := by
  intro n V _ _ Kf S ν v hG hfd hS hv hv0 hK a b hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.HW.exists_nat_weight_sub_eq_of_highest_vector_in_stable (ε := fun _ => true) (F := Kf)
      (Formalism.REAL.glRel_kRel (fun _ => true) Kf hG) (ne_of_lt hlt) rfl S (fun y hy => hS b a y hy)
      hv hv0 (hK.1 a) (hK.1 b) (hK.2 a b hlt rfl)
    have hm' : ν a - ν b = (m : ℝ) := by
      apply Complex.ofReal_injective
      push_cast
      exact hm
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith

end GlobalTheory.CompanionTheory.RealCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisMore
section
noncomputable section

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.KerZeroPf

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

theorem main : PositivityTheory.RgBcC.KerZero := by
  intro n _ _ μ _ E κ hκ hr hf y hy
  refine GlobalTheory.CompanionTheory.KerUniq.main n μ E κ (GLs n) GlobalTheory.CompanionTheory.KerUniq.isOpen_GLs subset_rfl ?_ hκ hr ?_ y hy
  · intro y hy k₂
    have hk : (k₂.1).det ≠ 0 := by
      have h : k₂.1 * star k₂.1 = 1 := (Matrix.mem_unitaryGroup_iff).1 k₂.2
      intro h0
      have h1 := congrArg Matrix.det h
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
      exact zero_ne_one h1
    show (y * k₂.1).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hy hk
  · intro f hfE hc _
    have h := hf f hfE hc
    simpa [act] using h

end GlobalTheory.CompanionTheory.KerZeroPf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedProductDropZeroFactorsStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_product_drop_zero_factors : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N), Nonempty ((prodIrr y hd).Equiv (prodIrr (fun a => y (o a)) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.ProdDrop.prodIrr_drop | exact GlobalTheory.CompanionTheory.FineProd.ProdDrop.prodIrr_drop | (intros; apply GlobalTheory.CompanionTheory.FineProd.ProdDrop.prodIrr_drop <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetTwoFactorCentralCharacterMulStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_two_factor_central_character_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), ∀ (x : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Zc.jm x hd π ≠ 0 → ∀ (t : kˣ) (c c0 c1 : ℂ), (∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v) → Zl.ScalarBy (x 0) t c0 → Zl.ScalarBy (x 1) t c1 → c0 * c1 = c := by
  first | exact @GlobalTheory.CompanionTheory.JacCentral.scalar_mul_eq | exact GlobalTheory.CompanionTheory.JacCentral.scalar_mul_eq | (intros; apply GlobalTheory.CompanionTheory.JacCentral.scalar_mul_eq <;> assumption)
end

