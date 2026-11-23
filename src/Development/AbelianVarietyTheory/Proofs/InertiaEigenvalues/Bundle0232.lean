module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import ReciprocityTheory.DualLattices.Bundle0023
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegral
section
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem exists_form_extending_coord {R F T V ι : Type} [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] [AddCommGroup T] [Module R T] [AddCommGroup V] [Module R V]
    [Module F V] [IsScalarTower R F V] (b : Module.Basis ι R T) (f : T →ₗ[R] V)
    (hf : Function.Injective f) (i : ι) :
    ∃ φ : V →ₗ[F] F, ∀ x, φ (f x) = algebraMap R F (b.repr x i) := by
  classical
  set v : ι → V := fun j => f (b j) with hv
  have hR : LinearIndependent R v := b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  have hF : LinearIndependent F v := (LinearIndependent.iff_fractionRing R F).mp hR
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hF).coord i)
  refine ⟨g, fun x => ?_⟩
  have hx : f x = ∑ j ∈ (b.repr x).support, algebraMap R F (b.repr x j) • v j := by
    conv_lhs => rw [← b.linearCombination_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, algebraMap_smul]
  have hy : f x = ((∑ j ∈ (b.repr x).support,
      algebraMap R F (b.repr x j) • Module.Basis.span hF j : Submodule.span F (Set.range v)) : V) := by
    rw [hx, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, Module.Basis.span_apply]
  have h2 := LinearMap.congr_fun hg
    (∑ j ∈ (b.repr x).support, algebraMap R F (b.repr x j) • Module.Basis.span hF j)
  rw [LinearMap.comp_apply, Submodule.subtype_apply] at h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hy, h2, map_sum]
  simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [Finsupp.mem_support_iff, not_not] at h
    rw [h, map_zero]

theorem continuous_form_of_moduleTopology {F L V : Type} [NontriviallyNormedField F]
    [CompleteSpace F] [Field L] [Algebra F L] [FiniteDimensional F L] [TopologicalSpace L]
    [IsTopologicalRing L] [T2Space L] [ContinuousSMul F L] [AddCommGroup V] [Module L V]
    [Module F V] [IsScalarTower F L V] [TopologicalSpace V] [IsModuleTopology L V]
    [FiniteDimensional L V] (φ : V →ₗ[F] F) : Continuous φ := by
  let e := (Module.finBasis L V).equivFun
  have he : Continuous e.toLinearMap := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  let ψ : (Fin (Module.finrank L V) → L) →ₗ[F] F := φ ∘ₗ (e.symm.toLinearMap.restrictScalars F)
  have hψ : Continuous ψ := LinearMap.continuous_of_finiteDimensional ψ
  have h : (φ : V → F) = ψ ∘ e.toLinearMap := by
    funext v
    simp [ψ]
  rw [h]
  exact hψ.comp he

variable {l : ℕ} [Fact l.Prime]

def zCHom (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* PadicComplex l :=
  (algebraMap ℚ_[l] (PadicComplex l)).comp (algebraMap ℤ_[l] ℚ_[l])

theorem zCHom_apply (x : ℤ_[l]) : zCHom l x = zC x := rfl

section Generic

variable {G R F L O : Type} [Group G] [TopologicalSpace G] [CommRing R] [Field F] [Field L]
  [Algebra F L] [CommRing O] [Algebra O L] [TopologicalSpace L] [Algebra R O]

def mulLat (R : Type) [CommRing R] [Algebra R O] (T : LocLat G F L O) (a : O) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ↥T.L.T →ₗ[R] ↥T.L.T :=
  letI := Module.compHom ↥T.L.T (algebraMap R O)
  { toFun := fun x => ⟨_, T.L.T.smul_mem a x.2⟩
    map_add' := fun x y => smul_add a x y
    map_smul' := fun c x => smul_comm a (algebraMap R O c) x }

theorem mulLat_apply (T : LocLat G F L O) (a : O) (x : ↥T.L.T) :
    mulLat R T a x = ⟨_, T.L.T.smul_mem a x.2⟩ := rfl

theorem coe_actT (T : LocLat G F L O) (g : G) (x : ↥T.L.T) :
    (actT T.L g x).1 = T.ρ g x.1 := rfl

theorem actT_mulLat (T : LocLat G F L O) (g : G) (a : O) (x : ↥T.L.T) :
    actT T.L g (mulLat R T a x) = mulLat R T a (actT T.L g x) := by
  rw [mulLat_apply, mulLat_apply]
  exact (actT T.L g).map_smul a x

theorem exists_basis_lat [Nontrivial R] [Module.Free R O] [Module.Finite R O]
    (T : LocLat G F L O) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∃ d : ℕ, Nonempty (Module.Basis (Fin d) R ↥T.L.T) := by
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  have : IsScalarTower R O ↥T.L.T := ⟨fun r o x => by
    show (r • o) • x = algebraMap R O r • (o • x)
    rw [Algebra.smul_def, mul_smul]⟩
  have : Module.Free O ↥T.L.T := T.L.free
  have : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  have : Module.Free R ↥T.L.T :=
    Module.Free.of_basis ((Module.Free.chooseBasis R O).smulTower (Module.Free.chooseBasis O ↥T.L.T))
  have : Module.Finite R ↥T.L.T := Module.Finite.trans O ↥T.L.T
  exact ⟨_, ⟨Module.finBasis R ↥T.L.T⟩⟩

theorem exists_form_lat [IsDomain R] [Algebra R F] [IsFractionRing R F]
    (hc : ∀ c : R, algebraMap O L (algebraMap R O c) = algebraMap F L (algebraMap R F c))
    (T : LocLat G F L O) {ι : Type} :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ (b : Module.Basis ι R ↥T.L.T) (i : ι),
      ∃ φ : T.V →ₗ[F] F, ∀ x : ↥T.L.T, φ x.1 = algebraMap R F (b.repr x i) := by
  intro b i
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  let _ : Module R T.V := Module.compHom T.V (algebraMap R F)
  have : IsScalarTower R F T.V := ⟨fun r c v => by
    show (r • c) • v = algebraMap R F r • (c • v)
    rw [Algebra.smul_def, mul_smul]⟩
  let f : ↥T.L.T →ₗ[R] T.V :=
    { toFun := fun x => x.1
      map_add' := fun x y => rfl
      map_smul' := fun r x => by
        show algebraMap R O r • x.1 = algebraMap R F r • x.1
        rw [← algebraMap_smul L (algebraMap R O r) x.1, hc, algebraMap_smul] }
  exact exists_form_extending_coord b f Subtype.val_injective i

def actLat (R : Type) [CommRing R] [Algebra R O] (T : LocLat G F L O) (g : G) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ↥T.L.T →ₗ[R] ↥T.L.T :=
  letI := Module.compHom ↥T.L.T (algebraMap R O)
  { toFun := actT T.L g
    map_add' := map_add _
    map_smul' := fun c x => (actT T.L g).map_smul (algebraMap R O c) x }

theorem matrices_lat {C : Type} [CommRing C] (z : R →+* C) (T : LocLat G F L O) {d : ℕ}
    (M : G → Matrix (Fin d) (Fin d) C) (A : O → Matrix (Fin d) (Fin d) C) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ b : Module.Basis (Fin d) R ↥T.L.T,
      (∀ g i j, M g i j = z (b.repr (actT T.L g (b j)) i)) →
      (∀ a i j, A a i j = z (b.repr (⟨_, T.L.T.smul_mem a (b j).2⟩ : ↥T.L.T) i)) →
      (∀ g h, M (g * h) = M g * M h) ∧ M 1 = 1 ∧ ∀ g a, M g * A a = A a * M g := by
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  intro b hM hA
  have kM : ∀ g, M g = (LinearMap.toMatrix b b (actLat R T g)).map z := by
    intro g; ext i j; rw [hM, Matrix.map_apply, LinearMap.toMatrix_apply]; rfl
  have kA : ∀ a, A a = (LinearMap.toMatrix b b (mulLat R T a)).map z := by
    intro a; ext i j; rw [hA, Matrix.map_apply, LinearMap.toMatrix_apply]; rfl
  have hmul : ∀ g h, actLat R T (g * h) = actLat R T g * actLat R T h := by
    intro g h
    refine LinearMap.ext fun x => Subtype.ext ?_
    show T.ρ (g * h) x.1 = T.ρ g (T.ρ h x.1)
    rw [map_mul]; rfl
  have hone : actLat R T 1 = 1 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show T.ρ 1 x.1 = x.1
    rw [map_one]; rfl
  have hcomm : ∀ g a, actLat R T g * mulLat R T a = mulLat R T a * actLat R T g :=
    fun g a => LinearMap.ext fun x => actT_mulLat (R := R) T g a x
  refine ⟨fun g h => ?_, ?_, fun g a => ?_⟩
  · rw [kM, kM, kM, hmul, LinearMap.toMatrix_mul, Matrix.map_mul]
  · rw [kM, hone, LinearMap.toMatrix_one]
    exact Matrix.map_one _ z.map_zero z.map_one
  · rw [kM, kA, ← Matrix.map_mul, ← Matrix.map_mul, ← LinearMap.toMatrix_mul,
      ← LinearMap.toMatrix_mul, hcomm]

end Generic

theorem continuous_coord_lat {G R F L O : Type} [Group G] [TopologicalSpace G] [CommRing R]
    [NontriviallyNormedField F] [CompleteSpace F] [Field L] [Algebra F L] [CommRing O]
    [Algebra O L] [TopologicalSpace L] [Algebra R O] [FiniteDimensional F L]
    [IsTopologicalRing L] [T2Space L] [ContinuousSMul F L]
    [IsDomain R] [Algebra R F] [IsFractionRing R F]
    (hc : ∀ c : R, algebraMap O L (algebraMap R O c) = algebraMap F L (algebraMap R F c))
    (T : LocLat G F L O) {ι : Type} :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ (b : Module.Basis ι R ↥T.L.T) (x : ↥T.L.T) (i : ι),
      Continuous fun g : G => algebraMap R F (b.repr (actT T.L g x) i) := by
  intro b x i
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  obtain ⟨φ, hφ⟩ := exists_form_lat (R := R) hc T b i
  have hφc : Continuous φ := continuous_form_of_moduleTopology (L := L) φ
  have h : (fun g : G => algebraMap R F (b.repr (actT T.L g x) i)) = fun g => φ (T.ρ g x.1) := by
    funext g
    rw [← hφ, coe_actT]
  rw [h]
  exact hφc.comp (T.cont x.1)

theorem exists_basis_lattice {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l)
    (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    letI := zlMod LL T
    ∃ d : ℕ, Nonempty (Module.Basis (Fin d) ℤ_[l] ↥T.L.T) := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 := integralClosure.isIntegralClosure ℤ_[l] ↥LL.1
  have : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] (↥LL.1) (↥(OL LL))
  have : Module.IsTorsionFree ℤ_[l] ↥LL.1 := Module.IsTorsionFree.trans_faithfulSMul ℤ_[l] ℚ_[l] _
  have : Module.Free ℤ_[l] ↥(OL LL) :=
    IsIntegralClosure.module_free ℤ_[l] ℚ_[l] (↥LL.1) (↥(OL LL))
  exact exists_basis_lat (R := ℤ_[l]) T

theorem isMat_exists_and_props : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∃ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A) ∧ ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → (∀ i j, ContinuousOn (fun σ => M σ i j) (GK K)) ∧ (∀ σ ∈ GK K, ∀ τ ∈ GK K, M (σ * τ) = M σ * M τ) ∧ M 1 = 1 ∧ (∀ σ ∈ GK K, ∀ a, M σ * A a = A a * M σ) := by
  intro l _ K LL T
  classical
  let _ : Module ℤ_[l] ↥T.L.T := zlMod LL T
  have hc : ∀ c : ℤ_[l], algebraMap (↥(OL LL)) (↥LL.1) (algebraMap ℤ_[l] (↥(OL LL)) c) =
      algebraMap ℚ_[l] (↥LL.1) (algebraMap ℤ_[l] ℚ_[l] c) := fun c => rfl
  refine ⟨?_, ?_⟩
  · obtain ⟨d, ⟨b⟩⟩ := exists_basis_lattice (G := ↥(GK K)) LL T
    refine ⟨d, fun σ => Matrix.of fun i j =>
        if h : σ ∈ GK K then zC (b.repr (actT T.L ⟨σ, h⟩ (b j)) i) else 0,
      fun a => Matrix.of fun i j => zC (b.repr (⟨_, T.L.T.smul_mem a (b j).2⟩ : ↥T.L.T) i),
      b, fun g i j => ?_, fun a i j => rfl⟩
    show (if h : (g : GQ l) ∈ GK K then zC (b.repr (actT T.L ⟨g, h⟩ (b j)) i) else 0) = _
    exact dif_pos g.2
  · intro d M A hMA
    obtain ⟨b, hM, hA⟩ := hMA
    have key := matrices_lat (R := ℤ_[l]) (F := ℚ_[l]) (L := ↥LL.1) (zCHom l) T
      (fun g : ↥(GK K) => M g) A b (fun g i j => (hM g i j).trans (zCHom_apply _).symm)
      (fun a i j => (hA a i j).trans (zCHom_apply _).symm)
    refine ⟨fun i j => ?_, fun σ hσ τ hτ => key.1 ⟨σ, hσ⟩ ⟨τ, hτ⟩, key.2.1,
      fun σ hσ a => key.2.2 ⟨σ, hσ⟩ a⟩
    rw [continuousOn_iff_continuous_domRestrict]
    have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    have h1 := continuous_coord_lat (R := ℤ_[l]) (F := ℚ_[l]) (L := ↥LL.1) (O := ↥(OL LL)) hc T b
      (b j) i
    have h2 : Continuous (algebraMap ℚ_[l] (PadicComplex l)) := continuous_algebraMap _ _
    refine (h2.comp h1).congr fun g => ?_
    exact ((hM ⟨g.1, g.2⟩ i j).trans (zCHom_apply _).symm).symm

end GlobalTheory.Cyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFilGradedSymbolToTateTwist
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

noncomputable section

namespace GlobalTheory.DeRhamSymbol

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem mem_iff (K : FinExt l) (a : ℤ) (x : P.R.BdR) :
    x ∈ (P.PD K).Fil a ↔ x ∈ (P.PD (botExt l)).Fil a := by
  have h := P.PD_Fil K (botExt l) a
  rw [← SetLike.mem_coe, h, SetLike.mem_coe]

theorem om_mem (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ (P.PD (botExt l)).Fil 0 := by
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, x ∈ K.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩,
    IntermediateField.mem_adjoin_simple_self _ x⟩
  have h := ((P.PD K).Fil 0).smul_mem ⟨x, hK⟩ (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one] at h
  exact (mem_iff K 0 _).1 h

theorem t_isUnit (P : LocPrime l) : IsUnit (P.ιB P.tB) := by
  have hu := (P.PD (botExt l)).t_unit
  rw [P.period_datum_t_eq] at hu
  exact hu.map P.ιB

def tU (P : LocPrime l) : P.R.BdRˣ := (t_isUnit P).unit

theorem tU_val : ((tU P : P.R.BdRˣ) : P.R.BdR) = P.ιB P.tB := rfl

theorem act_mem {a : ℤ} (g : GQ l) {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil a) :
    P.actQdR g x ∈ (P.PD (botExt l)).Fil a := by
  have := (P.PD (botExt l)).Fil_G ⟨g, mem_GK_bot g⟩ a x hx
  rwa [P.PD_actdR] at this

theorem actQdR_periodT_eq_cyclotomic_bottom (g : GQ l) :
    P.actQdR g (P.ιB P.tB) = algebraMap ℚ_[l] P.R.BdR (P.χQ g) * P.ιB P.tB := by
  have h := (P.PD (botExt l)).t_act ⟨g, mem_GK_bot g⟩
  rw [P.PD_actB, P.period_datum_t_eq, P.PD_χ] at h
  have h3 := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_bot g⟩ P.tB
  rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at h3
  rw [← h3, h, map_smul, Algebra.smul_def]

theorem act_zpow (g : GQ l) (n : ℤ) :
    P.actQdR g ((tU P ^ n : P.R.BdRˣ) : P.R.BdR) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ n : ℚ_[l]ˣ) : ℚ_[l]) * ((tU P ^ n : P.R.BdRˣ) : P.R.BdR) := by
  have h : Units.map ((P.actQdR g : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →* P.R.BdR) (tU P) =
      Units.map (algebraMap ℚ_[l] P.R.BdR : ℚ_[l] →* P.R.BdR) (P.χQ g) * tU P :=
    Units.ext (actQdR_periodT_eq_cyclotomic_bottom g)
  have h2 := congrArg (fun u : P.R.BdRˣ => ((u ^ n : P.R.BdRˣ) : P.R.BdR)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul] at h2
  rw [map_zpow P.χQ] at h2
  exact h2

variable {AI : LocAinf l P} (J : ThetaL P AI)
include J

theorem zpow_mem (n : ℤ) : ((tU P ^ n : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD (botExt l)).Fil n := by
  have h1 : ((tU P : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD (botExt l)).Fil 1 := by
    have := (P.PD (botExt l)).mem_filtration_one
    rwa [P.PD_ι, P.period_datum_t_eq] at this
  have h2 : (((tU P)⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD (botExt l)).Fil (-1) := by
    obtain ⟨y, hy, e⟩ := (J.fil_succ_iff_mul_t (-1) 1).1 (by simpa using (P.PD (botExt l)).one_mem)
    rw [← tU_val] at e
    rwa [Units.inv_eq_of_mul_eq_one_right e.symm]
  induction n using Int.induction_on with
  | zero => simpa using (P.PD (botExt l)).one_mem
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul]
    exact (P.PD (botExt l)).Fil_mul _ _ _ _ ih h1
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, sub_eq_add_neg]
    exact (P.PD (botExt l)).Fil_mul _ _ _ _ ih h2

theorem shift_iff (a b : ℤ) (x : P.R.BdR) :
    ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x ∈ (P.PD (botExt l)).Fil b ↔
      x ∈ (P.PD (botExt l)).Fil (a + b) := by
  constructor
  · intro h
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ (zpow_mem J a) h
    rwa [← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
      one_mul] at this
  · intro h
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ (zpow_mem J (-a)) h
    rwa [neg_add_cancel_left] at this


omit J in
theorem exists_symbol : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), ThetaL P AI →
    ∀ (K : FinExt l), ∃ sy : ℤ → P.R.BdR → PadicComplex l, ∀ a : ℤ,
      (∀ x ∈ (P.PD K).Fil a, ∀ y ∈ (P.PD K).Fil a, sy a (x + y) = sy a x + sy a y) ∧
      (∀ (c : Om l), ∀ x ∈ (P.PD K).Fil a,
        sy a (algebraMap (Om l) P.R.BdR c * x) = (c : PadicComplex l) * sy a x) ∧
      (∀ x ∈ (P.PD K).Fil a, sy a x = 0 ↔ x ∈ (P.PD K).Fil (a + 1)) ∧
      ∀ (g : GQ l), ∀ x ∈ (P.PD K).Fil a,
        sy a (P.actQdR g x) = chiC P.χQ a g * AI.actC g (sy a x) := by
  intro l _ P AI J K
  refine ⟨fun a x => J.θ (((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x), fun a => ?_⟩
  have key : ∀ x ∈ (P.PD K).Fil a,
      ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x ∈ (P.PD (botExt l)).Fil 0 := fun x hx =>
    (shift_iff J a 0 x).2 (by rw [add_zero]; exact (mem_iff K a x).1 hx)
  refine ⟨fun x hx y hy => ?_, fun c x hx => ?_, fun x hx => ?_, fun g x hx => ?_⟩
  · beta_reduce
    rw [mul_add, J.θ_add _ (key x hx) _ (key y hy)]
  · beta_reduce
    rw [mul_left_comm, J.θ_mul _ (om_mem c) _ (key x hx), J.θ_Om]
  · beta_reduce
    rw [J.θ_ker _ (key x hx), shift_iff J, mem_iff K]
  · beta_reduce
    have e : ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * P.actQdR g x =
        algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l])) *
          P.actQdR g (((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x) := by
      rw [← IsScalarTower.algebraMap_apply, map_mul, act_zpow, ← mul_assoc, ← mul_assoc,
        ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
        map_one, one_mul]
    rw [e, J.θ_mul _ (om_mem _) _ (act_mem g (key x hx)), J.θ_Om, J.θ_act g _ (key x hx)]
    rfl

end GlobalTheory.DeRhamSymbol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFactorialMulEqPowAinf
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem exists_factorial_mul_eq_pow (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∃ c : ℤ_[l], ((n.factorial : ℕ) : ℤ_[l]) * c = ((l : ℕ) : ℤ_[l]) ^ n := by
  have hp : l.Prime := Fact.out
  obtain ⟨k, m, hm, h⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero n) l hp.ne_one
  have hk : k ≤ n := by
    have h1 : k ≤ padicValNat l n.factorial :=
      ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (Nat.factorial_ne_zero n)).1 ⟨m, h⟩
    have h2 : (l - 1) * padicValNat l n.factorial = n - (l.digits n).sum := by
      simpa only [Nat.padicValNat_def] using hp.sub_one_mul_multiplicity_factorial (n := n)
    have h3 : 1 ≤ l - 1 := by have := hp.two_le; omega
    have h4 : padicValNat l n.factorial ≤ (l - 1) * padicValNat l n.factorial :=
      Nat.le_mul_of_pos_left _ h3
    omega
  have hu : IsUnit ((m : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨u * (l : ℤ_[l]) ^ j, ?_⟩
  rw [h]
  push_cast
  linear_combination ((l : ℤ_[l]) ^ (k + j)) * hu

theorem exists_factorial_mul_eq_pow_ainf (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∃ c : Ainf l, ((n.factorial : ℕ) : Ainf l) * c = ((l : ℕ) : Ainf l) ^ n := by
  obtain ⟨c, hc⟩ := exists_factorial_mul_eq_pow l n
  refine ⟨algebraMap ℤ_[l] (Ainf l) c, ?_⟩
  simpa only [map_mul, map_pow, map_natCast] using congrArg (algebraMap ℤ_[l] (Ainf l)) hc

end GlobalTheory.Per
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinf
section
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem actC_eq_σC (g : GQ l) (y : PadicComplex l) : AI.actC g y = Formalism.Per.σC g y := by
  have hc : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hc (by apply GlobalTheory.RingIface.sigC_cont)
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem actT_eq_σF (g : GQ l) (x : OCb l) : AI.actT g x = Formalism.Per.σF g x := by
  refine Perfection.ext fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g x n y hy.symm
  have h3 : y' = Formalism.Per.σO g y := Subtype.ext ((h1.trans (actC_eq_σC AI g y)).trans
    (by symm; apply GlobalTheory.RingIface.sigO_coe))
  refine h2.trans ?_
  rw [h3]
  exact (GlobalTheory.AdicMaps.coeff_galois l g x n y hy.symm).symm

theorem ζ_add_pow (j n : ℕ) : AI.ζ (j + n) ^ l ^ n = AI.ζ j := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]

theorem coeff_εroot (j n : ℕ) : PreTilt.coeff n (AI.εroot j) =
    Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (AI.ζ (j + n)) := by
  rw [← AI.ε_coeff, LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm, add_comm]

theorem untilt_εroot (j : ℕ) : (AI.εroot j).untilt = AI.ζ j := by
  refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : OC l)}) fun n => ?_
  refine ⟨AI.ζ (j + n), (coeff_εroot AI j n).symm, ?_⟩
  rw [ζ_add_pow]

theorem isTheta_fontaineTheta : IsTheta AI (WittVector.fontaineTheta (OC l) l) := by
  have hprim : IsPrimitiveRoot (((frobeniusEquiv (OCb l) l).symm AI.ε).untilt) l := by
    have h : ((frobeniusEquiv (OCb l) l).symm AI.ε).untilt = AI.ζ 1 := untilt_εroot AI 1
    rw [h]
    have h1 : AI.ζ 1 ^ l = 1 := (AI.ζ_succ 0).trans AI.ζ_zero
    have h2 := IsPrimitiveRoot.orderOf (AI.ζ 1)
    rwa [orderOf_eq_prime h1 AI.ζ_one] at h2
  refine ⟨fun x y h => ?_, ?_, fun g a => ?_, fun a => ?_, fun j => ?_⟩
  · rw [← Ideal.Quotient.eq, WittVector.fontaineTheta_teichmuller, ← h]
    exact PreTilt.mk_untilt_eq_coeff_zero x
  · exact ReciprocityTheory.PGsh.Ainf.theta_surj l (OC l) (PadicComplexInt.integers l)
  · have e : AI.actW g a = Formalism.Per.σA g a := WittVector.ext fun n =>
      (actT_eq_σF AI g (a.coeff n)).trans (by symm; apply GlobalTheory.RingIface.sigA_coeff)
    rw [e, actC_eq_σC]
    exact (congrArg Subtype.val (GlobalTheory.RingBasics.θ_σA g a)).trans (by apply GlobalTheory.RingIface.sigO_coe)
  · rw [← RingHom.mem_ker,
      ReciprocityTheory.PGsh.Ainf.ker_theta l (OC l) (PadicComplexInt.integers l) AI.ε hprim,
      Ideal.mem_span_singleton]
    rfl
  · rw [WittVector.fontaineTheta_teichmuller, untilt_εroot]

theorem exists_isTheta : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    ∃ θ : Ainf l →+* OC l, IsTheta AI θ :=
  fun _ _ _ AI => ⟨_, isTheta_fontaineTheta AI⟩

end GlobalTheory.Cyc
end
end

