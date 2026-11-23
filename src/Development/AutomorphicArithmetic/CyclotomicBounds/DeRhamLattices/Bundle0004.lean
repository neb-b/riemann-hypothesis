module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LatticePowerSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisComparisonAinfEqDeRhamComparison
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem _root_.UpperTheory.KN.crisComparison_ainf_eq_deRhamComparison :
    ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (w : Ainf l), GlobalTheory.BKGal.JumpDR.cB Td (acrisToBcris l (ainfToAcris l w)) = GlobalTheory.BKGal.JumpDR.cD Td (ainfToBdRp l w) := by
  intro l _ Pl AI Td w
  refine Td.eD.injective ?_
  have h := GlobalTheory.CrisIncl.incl_aB l _ Td.incl w
  refine Eq.trans h ?_
  exact (Td.eD.apply_symm_apply _).symm
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsPrimePowSmulMemLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem UpperTheory.KN.exists_pow_smul_mem_lattice_alt {l : ℕ} [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (v : T.V) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T :=
  _root_.UpperTheory.Reformulated.B.LatticePowerSmul.exists_pow_smul_mem_lattice_alt LL T v

theorem _root_.UpperTheory.KN.exists_prime_pow_smul_mem_lattice :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (v : T.V), ∃ (n : ℕ) (x : ↥T.L.T), (x : T.V) = ((l : ℚ_[l]) ^ n) • v := by
  intro l _ LL T v
  obtain ⟨n, hn⟩ := UpperTheory.KN.exists_pow_smul_mem_lattice_alt LL T v
  refine ⟨n, ⟨_, hn⟩, ?_⟩
  rw [← algebraMap_smul ↥LL.1 ((l : ℚ_[l]) ^ n) v, map_pow, map_natCast]
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.FilZeroEqRangeCDAndCDInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem mem_FilD_zero (l : ℕ) [Fact l.Prime] (x : Per.BdR l) :
    x ∈ Per.FilD l 0 ↔ ∃ y : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) y = x :=
  ⟨fun h => let ⟨z, _, e⟩ := GlobalTheory.RingIface.exists_of_mem_FilD_nat l (n := 0) h; ⟨z, e⟩,
    fun ⟨y, e⟩ => e ▸ GlobalTheory.RingIface.alg_mem_FilD_zero l y⟩

theorem _root_.UpperTheory.KN.fil_zero_eq_range_cD_and_cD_injective :
    ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (K : FinExt l), (∀ x : Pl.R.BdR, x ∈ (Pl.PD K).Fil 0 ↔ ∃ y : Per.BdRp l, x = GlobalTheory.BKGal.JumpDR.cD Td y) ∧ Function.Injective (GlobalTheory.BKGal.JumpDR.cD Td) := by
  intro l _ Pl AI Td K
  refine ⟨fun x => ?_, fun y z h => ?_⟩
  · rw [Td.fil, mem_FilD_zero]
    refine exists_congr fun y => ?_
    change _ ↔ x = Td.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) y)
    rw [RingEquiv.eq_symm_apply, eq_comm]
  · exact (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1 (Td.eD.symm.injective h)
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ITotEisensteinPowEqIDEisensteinHatPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem _root_.UpperTheory.KN.iTot_eisensteinPow_eq_iD_eisensteinHatPow :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (β : ℕ), toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun _ => ⟨E ↥LL.1 l e ^ β, pow_mem (E_mem l e _) β⟩)) = ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β := by
  intro l _ a e _ _ ϖ LL _ _ β
  refine (ϖ.iD_ofA (thetaW a LL) ↥LL.1 _).symm.trans ?_
  refine Eq.trans ?_ (map_pow (ϖ.iD (thetaW a LL) ↥LL.1) _ β)
  refine congrArg (ϖ.iD (thetaW a LL) ↥LL.1) ?_
  funext τ
  exact map_pow (ofA ↥(OL LL) ↥LL.1 l e) ⟨E ↥LL.1 l e, E_mem l e _⟩ β
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.InclLEisensteinPowPhiInvEqSingle
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.UpperTheory.KN.inclL_eisensteinPow_phiInv_eq_single : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (β : ℕ) (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1) (i : ι), inclL (thetaW a LL) ϖ P (fun j => ϖ.iTot (thetaW a LL) ↥LL.1 (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩)) = Pi.single i (inclO l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun _ => ⟨E ↥LL.1 l e ^ β, pow_mem (E_mem l e _) β⟩))) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P β hβ i
  ext i'
  rw [inclL_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, ← ϖ.iW_of_mem (thetaW a LL) ↥LL.1, frobMat, Matrix.map_apply,
    Matrix.of_apply, ← map_mul, ← map_sum]
  simp only [Pi.single_apply]
  have key : ∀ i' i τ, ∑ j, P.mx τ i' j * (E ↥LL.1 l e ^ β * P.mxInv τ j i) =
      E ↥LL.1 l e ^ β * (1 : Matrix ι ι _) i' i := by
    intro i' i τ
    rw [← P.mx_mul_mxInv τ, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  split_ifs with h
  · subst h
    refine congrArg _ (funext fun τ => Subtype.ext ?_)
    rw [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
    have h1 := key i' i' τ
    rw [Matrix.one_apply_eq, mul_one] at h1
    exact h1
  · have hz : ∀ F : ZMod a → invE l e (A ↥(OL LL) ↥LL.1), (∀ τ, ((F τ : invE l e (A ↥(OL LL) ↥LL.1)) : PowerSeries ↥LL.1) = 0) →
        ϖ.iW (thetaW a LL) ↥LL.1 F = 0 := fun F hF => by
      have hF0 : F = 0 := funext fun τ => Subtype.ext (hF τ)
      rw [hF0]
      exact map_zero _
    refine hz _ fun τ => ?_
    rw [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
    have h1 := key i' i τ
    rw [Matrix.one_apply_ne h, mul_zero] at h1
    exact h1
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LinearIndependentQlIntegerBasisSmulLatticeBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem linearIndependent_smul_basis_pairs {Z Q O L V κ σ : Type*} [CommRing Z] [Field Q] [Algebra Z Q] [IsFractionRing Z Q]
    [CommRing O] [Field L] [Algebra O L] [Algebra Z O] [Algebra Q L] [Algebra Z L]
    [IsScalarTower Z O L] [IsScalarTower Z Q L] [AddCommGroup V] [Module L V] [Module O V] [Module Q V]
    [IsScalarTower O L V] [IsScalarTower Q L V] (M : Submodule O V) (b : Module.Basis κ O M)
    (ω : Module.Basis σ Z O) :
    LinearIndependent Q (fun p : σ × κ => (algebraMap O L (ω p.1)) • ((b p.2 : M) : V)) := by
  letI : Module Z V := Module.compHom V (algebraMap Z L)
  haveI : IsScalarTower Z Q V := ⟨fun z q v => by
    show (z • q) • v = algebraMap Z L z • (q • v)
    rw [← algebraMap_smul L (z • q) v, ← algebraMap_smul L q v, smul_smul, Algebra.smul_def z q,
      map_mul, ← IsScalarTower.algebraMap_apply Z Q L]⟩
  haveI : IsScalarTower Z O V := ⟨fun z o v => by
    show (z • o) • v = algebraMap Z L z • (o • v)
    rw [Algebra.smul_def z o, mul_smul, ← algebraMap_smul L (algebraMap Z O z) (o • v),
      ← IsScalarTower.algebraMap_apply Z O L]⟩
  have hc : LinearIndependent O (fun k => ((b k : M) : V)) :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hZ : LinearIndependent Z (fun p : σ × κ => ω p.1 • ((b p.2 : M) : V)) :=
    linearIndependent_smul ω.linearIndependent hc
  have hQ := (LinearIndependent.iff_fractionRing Z Q).mp hZ
  have hf : (fun p : σ × κ => (algebraMap O L (ω p.1)) • ((b p.2 : M) : V)) =
      fun p => ω p.1 • ((b p.2 : M) : V) := funext fun p => algebraMap_smul L (ω p.1) _
  rw [hf]
  exact hQ

private theorem aux {Z Q O L V κ σ : Type*} [CommRing Z] [IsDomain Z] [Field Q] [Algebra Z Q] [IsFractionRing Z Q]
    [CommRing O] [IsDomain O] [Field L] [Algebra O L] [IsFractionRing O L] [Algebra Z O] [Algebra Q L] [Algebra Z L]
    [IsScalarTower Z O L] [IsScalarTower Z Q L] [AddCommGroup V] [Module L V] [Module O V] [Module Q V]
    [IsScalarTower O L V] [IsScalarTower Q L V] (M : Submodule O V) (b : Module.Basis κ O M) (ω : Module.Basis σ Z O) :
    LinearIndependent Q (fun p : σ × κ => (algebraMap O L (ω p.1)) • ((b p.2 : M) : V)) := by
  exact linearIndependent_smul_basis_pairs M b ω

theorem _root_.UpperTheory.KN.linearIndependent_Ql_integerBasis_smul_latticeBasis :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (κ σ : Type) [Fintype κ] [Fintype σ] (b : Module.Basis κ ↥(OL LL) ↥T.L.T) (ω : Module.Basis σ ℤ_[l] ↥(OL LL)), LinearIndependent ℚ_[l] (fun p : σ × κ => ((ω p.1 : ↥(OL LL)) : ↥LL.1) • ((b p.2 : ↥T.L.T) : T.V)) := by
  intro l _ LL T κ σ _ _ b ω
  exact linearIndependent_smul_basis_pairs (Z := ℤ_[l]) (Q := ℚ_[l]) (L := ↥LL.1) T.L.T b ω
end

