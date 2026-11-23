module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameSSModRepLatRepIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
public import Formalism.SharpRestriction.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0449
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0227
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0531
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlochKatoCocycleIffOrthogonalLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleModuleIffLatticeQuotients
section
noncomputable section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open Formalism.GaloisCohomology (scalRep)
open Formalism.MainNotions.N (GRep)
open scoped Pointwise

namespace GlobalTheory.FullCharpoly

section Ref
variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O) (t : ℕ)

def refInt : Representation O G (↥Γ.T₀.L.T × (Fin t → O)) :=
  Γ.W₀.prod (piRep fun c : Fin t => Γ.Wchi (c.val + 1))

theorem exists_refInt_equiv :
    ∃ e : QuotSMulTop Γ.lam (↥Γ.T₀.L.T × (Fin t → O)) ≃ₗ[O]
      (QuotSMulTop Γ.lam ↥Γ.T₀.L.T × (Fin t → QuotSMulTop Γ.lam O)),
      ∀ g x, e (modRep (refInt Γ t) Γ.lam g x) = Γ.refRep t g (e x) := by
  let p : (↥Γ.T₀.L.T × (Fin t → O)) →ₗ[O] (QuotSMulTop Γ.lam ↥Γ.T₀.L.T × (Fin t → QuotSMulTop Γ.lam O)) :=
    (Submodule.mkQ _).prodMap ((Submodule.mkQ _).compLeft (Fin t))
  have hp : ∀ x, p x = (Submodule.Quotient.mk x.1, fun c => Submodule.Quotient.mk (x.2 c)) :=
    fun _ => rfl
  refine StdAdm.exists_modRep_equiv _ _ _ p ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨a, b⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    choose b' hb' using fun c => Submodule.Quotient.mk_surjective _ (b c)
    exact ⟨(a, b'), Prod.ext rfl (funext hb')⟩
  · intro x
    rw [hp, Prod.ext_iff, funext_iff]
    simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨⟨a, ha⟩, hb⟩
      choose b hb using hb
      exact ⟨(a, b), Prod.ext ha (funext hb)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨⟨_, rfl⟩, fun c => ⟨_, rfl⟩⟩

theorem charpoly_refInt [Nontrivial O] [Module.Free O ↥Γ.T₀.L.T] [Module.Finite O ↥Γ.T₀.L.T] (g : G) :
    LinearMap.charpoly (refInt Γ t g) =
      LinearMap.charpoly (Γ.W₀ g) * ∏ c : Fin t, (X - C (Γ.chi (c.val + 1) g : O)) := by
  have h : refInt Γ t g = (Γ.W₀ g).prodMap
      (Matrix.toLin' (Matrix.diagonal fun c : Fin t => (Γ.chi (c.val + 1) g : O))) := by
    refine LinearMap.ext fun x => Prod.ext rfl (funext fun c => ?_)
    change (Γ.chi (c.val + 1) g : O) • x.2 c = Matrix.mulVec _ x.2 c
    rw [Matrix.mulVec_diagonal, smul_eq_mul]
  rw [h, LinearMap.charpoly_prodMap, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]

theorem sameSS_refRep_iff [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
    (hlam : Irreducible Γ.lam) {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [FiniteDimensional LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) :
    SameSS (modRep (latRep L) Γ.lam) (Γ.refRep t) ↔ ∀ g j, ∃ y : O,
      (LinearMap.charpoly (ρ g) - LinearMap.charpoly (Γ.T₀.ρ g) *
        ∏ c : Fin t, (X - C (algebraMap O LL (Γ.chi (c.val + 1) g)))).coeff j = algebraMap O LL (Γ.lam * y) := by
  have := L.free
  have := Γ.T₀.L.free
  have : Module.Finite O L.T := Module.Finite.iff_fg.2 L.fg
  have : Module.Finite O Γ.T₀.L.T := Module.Finite.iff_fg.2 Γ.T₀.L.fg
  obtain ⟨e, he⟩ := exists_refInt_equiv Γ t
  have h1 : SameSS (modRep (latRep L) Γ.lam) (Γ.refRep t) ↔
      SameSS (modRep (latRep L) Γ.lam) (modRep (refInt Γ t) Γ.lam) :=
    ⟨fun h => StdAdm.sameSS_of_equiv h e.symm fun g x => by
      rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply],
     fun h => StdAdm.sameSS_of_equiv h e he⟩
  rw [h1, GlobalTheory.RedCharpoly.sameSS_modRep_iff _ _ _ (PrincipalIdealRing.isMaximal_of_irreducible hlam)]
  refine forall_congr' fun g => forall_congr' fun j => exists_congr fun y => ?_
  have h2 : ∏ c : Fin t, (X - C (algebraMap O LL (Γ.chi (c.val + 1) g))) =
      (∏ c : Fin t, (X - C (Γ.chi (c.val + 1) g : O))).map (algebraMap O LL) := by
    simp [Polynomial.map_prod]
  rw [GlobalTheory.RedCharpoly.charpoly_lattice L, GlobalTheory.RedCharpoly.charpoly_lattice Γ.T₀.L, h2, ← Polynomial.map_mul,
    ← Polynomial.map_sub, Polynomial.coeff_map, charpoly_refInt]
  exact (IsFractionRing.injective O LL).eq_iff.symm

end Ref

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

theorem full_iff (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) :
    Full (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut T ↔ CrysWith (P.PD S.K) S.emb T.ρ S.D.Ut ∧ ∀ g j, ∃ y : S.O,
      (LinearMap.charpoly (T.ρ g) - LinearMap.charpoly (S.Γ.T₀.ρ g) *
        ∏ c : Fin S.D.t, (X - C (algebraMap S.O ↥S.LL.1 (S.Γ.chi (c.val + 1) g)))).coeff j =
          algebraMap S.O ↥S.LL.1 (S.Γ.lam * y) := by
  obtain ⟨⟨_, h1, h2⟩, -, -, h3, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  have hlam : Irreducible S.Γ.lam := S.hyp.1.2.2.2.2.2
  exact and_congr_right fun _ => ⟨fun h => (sameSS_refRep_iff S.Γ S.D.t hlam T.L).1 (h T.L),
    fun h L => (sameSS_refRep_iff S.Γ S.D.t hlam L).2 h⟩

theorem hasFiniteQuotients_padicInt : Ring.HasFiniteQuotients ℤ_[l] where
  finiteQuotient {I} hI := by
    obtain ⟨n, rfl⟩ := PadicInt.ideal_eq_span_pow_p hI
    rw [← PadicInt.ker_toZModPow]
    exact Finite.of_injective _ (RingHom.kerLift_injective (PadicInt.toZModPow n))

theorem hasFiniteQuotients_OL (LL : FinExt l) : Ring.HasFiniteQuotients ↥(OL LL) := by
  have := hasFiniteQuotients_padicInt (l := l)
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 (integralClosure ℤ_[l] ↥LL.1)
  exact Ring.HasFiniteQuotients.of_module_finite ℤ_[l] _

theorem finite_of_lattices {G LL O V M : Type} [Group G] [Field LL] [CommRing O] [IsDomain O] [Algebra O LL]
    [IsFractionRing O LL] [Ring.HasFiniteQuotients O] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] [AddCommGroup M] [Module O M] {ρ : Representation LL G V}
    (L₁ L₂ : Lattice (O := O) ρ) (p : ↥L₁.T →ₗ[O] M) (hp : Function.Surjective p)
    (hk : ∀ x : ↥L₁.T, (x : V) ∈ L₂.T → p x = 0) : Finite M := by
  have : Module.Finite O L₁.T := Module.Finite.iff_fg.2 L₁.fg
  have : Module.Finite O M := Module.Finite.of_surjective p hp
  have h1 : ∀ x : V, ∃ a : nonZeroDivisors O, (a : O) • x ∈ L₂.T := by
    intro x
    have hx : x ∈ Submodule.span LL (L₂.T : Set V) := by rw [L₂.span]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, by simpa using hx⟩
    | zero => exact ⟨1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a * b, ?_⟩
      rw [smul_add, Submonoid.coe_mul]
      refine L₂.T.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact L₂.T.smul_mem _ ha
      · rw [mul_smul]; exact L₂.T.smul_mem _ hb
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨⟨y, b⟩, hb⟩ := IsLocalization.surj (nonZeroDivisors O) c
      refine ⟨a * b, ?_⟩
      have : ((a * b : nonZeroDivisors O) : O) • c • x = y • ((a : O) • x) := by
        rw [Submonoid.coe_mul, mul_smul, smul_comm y, ← algebraMap_smul LL (b : O), smul_smul, mul_comm, hb,
          algebraMap_smul]
      rw [this]
      exact L₂.T.smul_mem _ ha
  have ht : Module.IsTorsion O M := by
    intro m
    obtain ⟨x, rfl⟩ := hp m
    obtain ⟨a, ha⟩ := h1 x
    exact ⟨a, by rw [Submonoid.smul_def, ← map_smul]; exact hk _ ha⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors ht
  have : Finite (O ⧸ Ideal.span {r}) := Ring.HasFiniteQuotients.finiteQuotient
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact nonZeroDivisors.ne_zero hr0)
  have hb : Ideal.span {r} • (⊤ : Submodule O M) = ⊥ :=
    Submodule.le_annihilator_iff.1 ((Ideal.span_singleton_le_iff_mem _).2 hr)
  have : Finite (M ⧸ Ideal.span {r} • (⊤ : Submodule O M)) :=
    Submodule.finite_quotient_smul _ Module.Finite.fg_top
  exact Finite.of_equiv _ (Submodule.quotEquivOfEqBot _ hb).toEquiv

attribute [local instance 10000] GRep.modO LocLat.modO GRep.towO LocLat.towO Submodule.module

theorem nonempty_lattice (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) : Nonempty (Lattice (O := S.O) A.ρ) := by
  obtain ⟨⟨_, h1, h2⟩, -, -, h3, h4⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  have := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK S.K
  exact GlobalTheory.CrysExt.exists_lattice h4 A.ρ A.cont

def PolyFull (jT : ZMod S.n → ℤ → ℤ) (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) : Prop :=
  IsCrys (P.PD S.K) A.ρ ∧
    (∀ i (τ : ↥S.K.1 →ₐ[ℚ_[l]] ↥S.LL.1), (∀ x : ↥(K0 S.K), τ (algebraMap _ _ x) = S.emb i x) →
      ∀ a : ℤ, multV (P.PD S.K) A.ρ τ a = jT i a) ∧
    ∀ g j, ∃ y : S.O, (LinearMap.charpoly (A.ρ g) - LinearMap.charpoly (S.Γ.T₀.ρ g) *
      ∏ c : Fin S.D.t, (X - C (algebraMap S.O ↥S.LL.1 (S.Γ.chi (c.val + 1) g)))).coeff j =
        algebraMap S.O ↥S.LL.1 (S.Γ.lam * y)

def toLoc (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) A.ρ) : LocLat S.G ℚ_[l] ↥S.LL.1 S.O where
  V := A.V
  ρ := A.ρ
  cont := A.cont
  L := L

def ofLoc (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) : GRep S.G ℚ_[l] ↥S.LL.1 S.O where
  V := T.V
  ρ := T.ρ
  cont := T.cont

theorem full_iff_polyFull {jT : ZMod S.n → ℤ → ℤ} (hj : ∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a)
    (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) :
    Full (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut T ↔ PolyFull S jT (ofLoc S T) := by
  rw [full_iff, CrysWith, and_assoc]
  simp only [HasJumps, hj]
  rfl


set_option synthInstance.maxHeartbeats 200000 in
theorem admissibleModule_iff_lattice_quotients {jT : ZMod S.n → ℤ → ℤ} (hj : ∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a)
    {M : Type} [AddCommGroup M] [Module S.O M] (π : Representation S.O S.G M) :
    S.admitted π ↔ ∃ (μ : ℕ) (F : Fin μ → GRep S.G ℚ_[l] ↥S.LL.1 S.O) (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O)
      (e : A.V ≃ₗ[↥S.LL.1] (∀ j, (F j).V)) (L₁ L₂ : Lattice (O := S.O) A.ρ) (p : ↥L₁.T →ₗ[S.O] M),
      (∀ j, PolyFull S jT (F j)) ∧ (∀ g x j, e (A.ρ g x) j = (F j).ρ g (e x j)) ∧ L₂.T ≤ L₁.T ∧
      Function.Surjective p ∧ (∀ g x, p (latRep L₁ g x) = π g (p x)) ∧ ∀ x, p x = 0 ↔ (x : A.V) ∈ L₂.T := by
  constructor
  · rintro ⟨-, μ, T, ⟨F, hF, e, he⟩, L₂, p, h1, h2, h3, h4⟩
    exact ⟨μ, fun j => ofLoc S (F j), ofLoc S T, e, T.L, L₂, p,
      fun j => (full_iff_polyFull S hj _).1 (hF j), he, h1, h2, h3, h4⟩
  · rintro ⟨μ, F, A, e, L₁, L₂, p, hF, he, h1, h2, h3, h4⟩
    obtain ⟨⟨_, -, h6⟩, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
    have := hasFiniteQuotients_OL S.LL
    exact ⟨finite_of_lattices L₁ L₂ p h2 fun x => (h4 x).2, μ, toLoc S A L₁,
      ⟨fun j => toLoc S (F j) (nonempty_lattice S (F j)).some,
        fun j => (full_iff_polyFull S hj _).2 (hF j), e, he⟩, L₂, p, h1, h2, h3, h4⟩

end GlobalTheory.FullCharpoly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmittedStatementsOfLocalBoundsConclusion
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem admittedStatements_of_localBoundsConclusion : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ),
    Concl L P X C → ∃ tb : TwistedPlaces.Tab L, TwistedPlaces.AdmT L tb C P := by
  intro D L P X C h
  obtain ⟨tf, hF, h23⟩ := h.two
  refine ⟨tab L X tf C, ?_⟩
  have h2 : TwistedPlaces.adm2 L := fun j hj w hw _ => h.mult j hj w hw
  obtain ⟨hA, hB, hC, hD, hBand⟩ := _root_.GlobalTheory.NLink.localBoundTableAllPrimes_rowsAndBand D L P X C tf h
  obtain ⟨hE, hExc⟩ := _root_.GlobalTheory.NLink.largePrimeLengthVanishing_and_exceptionalBounded_tab D L P X C tf h
  obtain ⟨hG, hH⟩ := _root_.GlobalTheory.NLink.localBoundTableAllPrimes_ramified_typePrimes D L P X C tf h
  exact ⟨h.pass, h2, h.rank, _root_.GlobalTheory.NLink.admissible_table_of_conclusion D L P X C tf h h23, _root_.GlobalTheory.NLink.adm5_tab D L P X C tf h,
    _root_.GlobalTheory.NLink.adm6_tab D L P X C tf h, hA, hB, hC, hD, hBand, hE, hExc,
    _root_.GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree D L P X C tf h hF, hG, hH, h.par⟩

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfTensorInj
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisRegular
variable {l : ℕ} [Fact l.Prime] (C : Core l)

theorem exists_frob (C : Core l) :
    ∃ F : GQ l, ∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l := by
  obtain ⟨g, hg⟩ := FrobLaws.exists_ext C.σ
  refine ⟨g, fun ζ m hm hlm hζ => ?_⟩
  let c : ↥(MaximalUnramifiedExtension l) := ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩⟩
  have := C.σ_root c m hm hlm (Subtype.ext hζ)
  rw [show ζ = (c : Om l) from rfl, hg, this]; rfl

theorem qB_coe (z : ℤ_[l]) : C.qB (z : ℚ_[l]) = Per.zB l z := (GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.1 z

theorem ι_aB (a : Per.Ainf l) :
    C.ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  rw [GlobalTheory.RingIface.aB_eq_alg, C.ι_j, GlobalTheory.RingIface.tower, C.j_cris.on0, Subalgebra.coe_algebraMap]
  simp only [aDp, RingHom.comp_apply]

theorem theta_eig {b : Per.Bcris l} {y : Per.BdRp l}
    (h : C.ι b = algebraMap (Per.BdRp l) (Per.BdR l) y) {g : GQ l} {x : ℚ_[l]}
    (hx : Per.σB g b = C.qB x * b) :
    Per.σC g (Per.θD l y) = algebraMap ℚ_[l] ℂ_[l] x * Per.θD l y := by
  have h1 := congrArg C.ι hx
  rw [(GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.2.2.1, map_mul, h, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1,
    show C.ι (C.qB x) = _ from C.ι_u _, ← map_mul] at h1
  have h2 := congrArg (Per.θD l) ((BdRField.bdR_isField l).2.1 h1)
  rw [(thetaD_props l).2.2.2.2, map_mul, C.o_sec.th] at h2
  exact h2

theorem σB_tB (g : GQ l) : Per.σB g C.tB = C.qB ((C.χ g : ℤ_[l]) : ℚ_[l]) * C.tB := by
  rw [qB_coe, Core.tB, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1, TAct.t_act l C g, map_mul,
    GlobalTheory.RingIface.zB_eq_aB_zA, GlobalTheory.RingIface.aB_eq_alg]

theorem isUnit_of_theta {b : Per.Bcris l} {y : Per.BdRp l}
    (h : C.ι b = algebraMap (Per.BdRp l) (Per.BdR l) y) (hy : Per.θD l y ≠ 0)
    (hb : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) : IsUnit b := by
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_unitCharacter_of_galoisStable_line_cLTate l _ hy fun g => (hb g).imp fun x hx => theta_eig C h hx
  obtain ⟨N, hN, hI⟩ := _root_.GlobalTheory.TateEigen.finite_on_inertia l η _ hy hη
  obtain ⟨F, hF⟩ := exists_frob C
  obtain ⟨w, hw, hwI, hwF, hwφ⟩ := _root_.GlobalTheory.MemLoc.exists_unramified_period l F hF (η F ^ N)⁻¹
  have h2 : C.ι (b ^ N * Per.aB l w) = algebraMap (Per.BdRp l) (Per.BdR l) (y ^ N * aDp l w) := by
    rw [map_mul, map_pow, h, ι_aB, map_mul, map_pow]
  have hθ : Per.θD l (y ^ N * aDp l w) ≠ 0 := by
    rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hy) ((hw.map _).map _).ne_zero
  have hact : ∀ g : GQ l, Per.σC g (Per.θD l (y ^ N * aDp l w)) =
      algebraMap ℚ_[l] ℂ_[l] (((η g ^ N : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) * Per.θD l y ^ N *
        Per.θD l (aDp l (Per.σA g w)) := by
    intro g
    rw [map_mul, map_mul, map_pow, map_pow, hη, ← (thetaD_props l).2.2.2.2,
      (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.1, mul_pow, ← map_pow, Units.val_pow_eq_pow_val,
      PadicInt.coe_pow]
  have hfix := _root_.GlobalTheory.RegularDense.fixed_of_inertia_frobenius l F hF (Per.θD l (y ^ N * aDp l w))
    (fun g hg => by rw [hact, hI g hg, hwI g hg]; simp)
    (by
      rw [hact, hwF, map_mul, map_mul, ← C.o_sec.z, C.o_sec.th, map_mul, map_pow]
      have e : algebraMap ℚ_[l] ℂ_[l] (((η F ^ N : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) *
          algebraMap ℚ_[l] ℂ_[l] ((((η F ^ N)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = 1 := by
        rw [← map_mul, ← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one, map_one]
      have e' : ((algebraMap ℚ_[l] (Om l) ((((η F ^ N)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) : Om l) : ℂ_[l]) =
        algebraMap ℚ_[l] ℂ_[l] ((((η F ^ N)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := rfl
      rw [e']
      linear_combination (Per.θD l y ^ N * Per.θD l (aDp l w)) * e)
  have hinv : ∀ g : GQ l, Per.σB g (b ^ N * Per.aB l w) = b ^ N * Per.aB l w := by
    intro g
    obtain ⟨x, hx⟩ := hb g
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.UnitLine.sigma_unit_eigen l w _ hw hwφ g
    have e : Per.σB g (b ^ N * Per.aB l w) = C.qB (x ^ N * z) * (b ^ N * Per.aB l w) := by
      rw [map_mul, map_pow, hx, hz, map_mul, map_pow, qB_coe]
      ring
    have e2 := theta_eig C h2 e
    rw [hfix] at e2
    have e3 : algebraMap ℚ_[l] ℂ_[l] (x ^ N * z) = 1 := mul_right_cancel₀ hθ (by rw [one_mul, ← e2])
    have e4 : x ^ N * (z : ℚ_[l]) = 1 := (algebraMap ℚ_[l] ℂ_[l]).injective (by rw [e3, map_one])
    rw [e, e4, map_one, one_mul]
  obtain ⟨c, -, hc⟩ := _root_.GlobalTheory.MemLoc.InvCris.invariants_Bcris l C ⟨⊥, inferInstance⟩ _ fun g _ => hinv g
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [← hc, map_zero, map_zero] at h2
    apply hθ
    rw [(BdRField.bdR_isField l).2.1 (h2.symm.trans (map_zero _).symm), map_zero]
  have hu : IsUnit (b ^ N * Per.aB l w) := hc ▸ (Ne.isUnit hc0).map C.u
  exact (isUnit_pow_iff hN.ne').1 (isUnit_of_mul_isUnit_left hu)

theorem isUnit_of_line (b : Per.Bcris l) (h0 : b ≠ 0)
    (hb : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) : IsUnit b := by
  obtain ⟨m, n, b', y, e, hy, hθ⟩ := _root_.GlobalTheory.MemLoc.RegDivide.exists_divide l C b h0
  have ht : IsUnit C.tB := (core_t_unit_fil l C).1
  have hu : IsUnit b' := isUnit_of_theta C hy hθ fun g => by
    obtain ⟨x, hx⟩ := hb g
    set a : ℚ_[l] := ((C.χ g : ℤ_[l]) : ℚ_[l]) with ha
    have ha0 : a ≠ 0 := by
      rw [ha]
      exact PadicInt.coe_ne_zero.2 (C.χ g).ne_zero
    refine ⟨x * a ^ m * (a ^ n)⁻¹, ?_⟩
    have e1 := congrArg (Per.σB g) e
    rw [map_mul, map_mul, map_pow, map_pow, hx, σB_tB, ← ha] at e1
    have e2 : C.qB a ^ n * C.qB (a ^ n)⁻¹ = 1 := by
      rw [← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ ha0), map_one]
    apply (ht.pow n).mul_left_cancel
    rw [map_mul, map_mul, map_pow]
    linear_combination (-C.qB (a ^ n)⁻¹) * e1 + (C.qB x * C.qB a ^ m * C.qB (a ^ n)⁻¹) * e -
      (C.tB ^ n * Per.σB g b') * e2
  exact isUnit_of_mul_isUnit_left (e ▸ (ht.pow n).mul hu)

end GlobalTheory.MemLoc.CrisRegular

namespace GlobalTheory.MemLoc

theorem core_regular (l : ℕ) [Fact l.Prime] (C : Core l) : C.Regular :=
  _root_.GlobalTheory.MemLoc.regular_of_full l C (CrisRegular.isUnit_of_line C)

theorem regular_of_tensorInj : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.TensorInj → C.Regular :=
  fun l _ C _ => core_regular l C

end GlobalTheory.MemLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDiscCocycleFrobeniusEquationStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_disc_cocycle_frobenius_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d M N : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S) → bk.ev bk.E ^ N • Y.map WittVector.frobenius = bk.ev bk.E ^ M • (Y * A.map bk.ev) → (Y.map bk.iA).det ≠ 0 → ∀ (g : GQ l) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ∀ (w : (Ainf l)ˣ), Per.σA g (bk.ev bk.E) = bk.ev bk.E * w → ∀ (P : Matrix (Fin d) (Fin d) (Ainf l)), P.map WittVector.frobenius = P → ∀ (e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), bk.iA (Per.σA g τ) ^ M • (Y.map bk.iA * e) = bk.iA τ ^ M • (P.map bk.iA * (Y.map (Per.σA g)).map bk.iA) → bk.iS bk.E ^ (2 * N) • e = (((↑w⁻¹ : Ainf l) ^ N) • A.map bk.ev).map bk.iA * e.map Φ * ((A'.map bk.ev).map (Per.σA g)).map bk.iA := by
  first | (exact @GlobalTheory.BSP.CocycleFrob.frob_eq) | (exact GlobalTheory.BSP.CocycleFrob.frob_eq) | (intros; apply GlobalTheory.BSP.CocycleFrob.frob_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDiscExistsConstAddXMulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinDisc_exists_const_add_X_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ (κ : Disc l (0 : Wq l bk.a) 1 →+* bk.DS ρ), IsDiscMap (l := _) (u := _) (ρ := _) (C : Wq l bk.a →+* bk.S) κ → ∀ x : bk.DS ρ, ∃ (c : Disc l (0 : Wq l bk.a) 1) (x₁ : bk.DS ρ), x = κ c + toDisc l (X : bk.S) ρ X * x₁ := by
  first | (exact @GlobalTheory.BSP.exists_const_add_X_mul_disc) | (exact GlobalTheory.BSP.exists_const_add_X_mul_disc) | (intros; apply GlobalTheory.BSP.exists_const_add_X_mul_disc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousDualMat
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pass.LocDirect

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def dualMat {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) (Br.LL D.nbr i w hw) :=
  GlobalTheory.TateDualX.dualTw (cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw)) (Br.loc D.nbr i w hw M)

theorem dualMat_apply {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    dualMat i w hw M g = ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) :
      Br.LL D.nbr i w hw) • (Br.loc D.nbr i w hw M g⁻¹).transpose := rfl

theorem continuous_dualMat {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) : Continuous (dualMat i w hw M) := by
  haveI := isTopRing i w hw
  exact GlobalTheory.TateDualX.continuous_dualTw _ _ (GlobalTheory.TateDualX.continuous_cyc D i w hw)
    (GlobalTheory.PotDual.continuous_loc D i w hw M hM)

def Udual {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  haveI := isTopRing i w hw
  GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (dualMat i w hw M) (continuous_dualMat i w hw M hM)

theorem cyc_mem (g : Br.G D.nbr i w hw) : ∃ c : Br.OLL D.nbr i w hw,
    algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) c =
      ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) := by
  rw [← GlobalTheory.CycBridge.locChi_epsU_eq_cycLL D i w hw]
  exact ⟨_, rfl⟩

theorem dualMat_integral {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    ∃ N : Matrix (Fin k) (Fin k) (Br.OLL D.nbr i w hw),
      dualMat i w hw M g = N.map (algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw)) := by
  obtain ⟨c, hc⟩ := cyc_mem i w hw g
  refine ⟨c • (Br.locO (D.nbr i w hw) (M.comp (decS D.nd w)) g⁻¹).transpose, ?_⟩
  rw [dualMat_apply, ← hc, Matrix.map_smul' _ _ _ (map_mul _), Matrix.transpose_map]
  rfl

def latDual {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) :
    Lattice (O := Br.OLL D.nbr i w hw) (Udual i w hw M hM).ρ :=
  GlobalTheory.BKLatticeCochain.stdLattice Subtype.val_injective (Udual i w hw M hM).ρ fun g => by
    obtain ⟨N, hN⟩ := dualMat_integral i w hw M g
    exact ⟨N, fun x => by rw [← hN]; rfl⟩

end GlobalTheory.Pass.LocDirect

end
end

