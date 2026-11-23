module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCharSurjectiveAndMapRangeAl
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyCechVanishingAboveDegree
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

theorem not_NV_of_ge :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
      ∃ c : ℕ, ∀ P : LB A.left, P.IsLB → ∀ j : ℕ, c ≤ j → ¬ NV A P j := by
  intro K _ _ A _ hA
  haveI : IsProper A.hom := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hsep : IsSeparated A.hom := inferInstance
  obtain ⟨m, V, hV, hc⟩ :=
    GlobalTheory.exists_fin_affine_cover (X := A.left) (V := ⊤) (by simpa using isCompact_univ)
  refine ⟨m, fun P hP j hj hNV => ?_⟩
  obtain ⟨κ, _, _, W, hW, hWc, hne⟩ := hNV
  obtain ⟨e⟩ := GlobalTheory.AbLaw.cechLB_homology_equiv_of_affine_covers K A.left A.hom P κ W (Fin m) V
    hP hsep hW hWc hV hc j
  apply hne
  have hz : IsZero ((GlobalTheory.AbLaw.cechLB A.hom P V).X j) :=
    GlobalTheory.AbLaw.isZero_cechLB_X A.hom P V (by simpa using hj)
  have h0 : IsZero ((GlobalTheory.AbLaw.cechLB A.hom P V).homology j) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (HomologicalComplex.ExactAt.of_isZero hz)
  have : Subsingleton ((GlobalTheory.AbLaw.cechLB A.hom P V).homology j) :=
    ModuleCat.isZero_iff_subsingleton.1 h0
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (ModuleCat.isZero_iff_subsingleton.2 e.toEquiv.subsingleton)

end GlobalTheory.AmpleGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMinpolyCoeffZeroPowNumberField
section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.NormTower

open IntermediateField

theorem abs_norm_coeff_zero_pow (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (β : ℂ) (p : K[X])
    (h : GlobalTheory.FunObj.SqNum.IsMinPol σ β p) (hβ : IsAlgebraic ℚ β) :
    |(Algebra.norm ℚ (p.coeff 0) : ℚ)| ^ (minpoly ℚ β).natDegree =
      |(minpoly ℚ β).coeff 0| ^ (p.natDegree * Module.finrank ℚ K) := by
  obtain ⟨hm, hirr, hev⟩ := h
  haveI := Fact.mk hirr
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  haveI : Module.Finite K (AdjoinRoot p) := pb.finite
  haveI : FiniteDimensional ℚ (AdjoinRoot p) := Module.Finite.trans K (AdjoinRoot p)
  set r := AdjoinRoot.root p
  have hNK : Algebra.norm K r = (-1) ^ p.natDegree * p.coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    rwa [AdjoinRoot.minpoly_powerBasis_gen_of_monic hm, AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim] at this
  let φ : AdjoinRoot p →+* ℂ := AdjoinRoot.lift σ β hev
  have hφ : φ r = β := AdjoinRoot.lift_root hev
  have hmin : minpoly ℚ r = minpoly ℚ β := by
    rw [← hφ]; exact (minpoly.algHom_eq φ.toRatAlgHom φ.injective r).symm
  have hint : IsIntegral ℚ r := .of_finite ℚ r
  have h1 : Algebra.norm ℚ r = Algebra.norm ℚ ((-1) ^ p.natDegree * p.coeff 0 : K) := by
    rw [← hNK, Algebra.norm_norm]
  have h2 := Algebra.norm_eq_norm_adjoin ℚ r
  have h3 : Algebra.norm ℚ (IntermediateField.AdjoinSimple.gen ℚ r) =
      (-1) ^ (minpoly ℚ β).natDegree * (minpoly ℚ β).coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hint)
    rw [IntermediateField.adjoin.powerBasis_gen hint, IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim, hmin] at this
    exact this
  have hdeg : Module.finrank ℚ (AdjoinRoot p) = p.natDegree * Module.finrank ℚ K := by
    rw [← Module.finrank_mul_finrank ℚ K (AdjoinRoot p), pb.finrank, AdjoinRoot.powerBasis_dim, mul_comm]
  have hdeg2 : Module.finrank ℚ (AdjoinRoot p) = (minpoly ℚ β).natDegree * Module.finrank ℚ⟮r⟯ (AdjoinRoot p) := by
    rw [← Module.finrank_mul_finrank ℚ ℚ⟮r⟯ (AdjoinRoot p), IntermediateField.adjoin.finrank hint, hmin]
  have hn1 : |Algebra.norm ℚ (-1 : K)| = 1 := by
    rw [show (-1 : K) = algebraMap ℚ K (-1) by simp, Algebra.norm_algebraMap]; simp
  have key : |Algebra.norm ℚ (p.coeff 0)| = |(minpoly ℚ β).coeff 0| ^ Module.finrank ℚ⟮r⟯ (AdjoinRoot p) := by
    have e := congrArg abs (h1.symm.trans (h2.trans (congrArg (· ^ Module.finrank ℚ⟮r⟯ (AdjoinRoot p)) h3)))
    rw [map_mul, map_pow, abs_mul, abs_pow, hn1, one_pow, one_mul, abs_pow, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul] at e
    exact e
  rw [key, ← pow_mul, mul_comm, ← hdeg2, hdeg]

end GlobalTheory.NormTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlCSurjectiveAndLinearIndependentBLie
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

theorem alC_surjective_and_linearIndependent_bLie :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), HTChar p v P.Gt → Function.Surjective P.alC ∧ ∀ (n : ℕ) (x : Fin n → LieG P.Gt), LinearIndependent C (fun j => evLie P (x j)) → LinearIndependent C (fun j => P.bLie (x j)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P hHT
  have hp : p.Prime := Fact.out
  have h0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hs : Function.Surjective P.alC := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    rintro w -
    induction w using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | tmul c f =>
      have h1 : v (algebraMap O C (p : O)) ^ (p - 1) ≤ v (p : C) := by
        have hle := P.integers.map_le_one (p : O)
        rw [map_natCast] at hle ⊢
        exact pow_le_of_le_one zero_le hle (by have := hp.two_le; omega)
      have h2 := hHT (p : O) h1 f.1 f.2
      rw [← (weilChar_surjective_and_map_range_al p C v O Λ P).2] at h2
      obtain ⟨_, ⟨t, rfl⟩, ht⟩ := h2
      have h3 : P.al t = (p : O) • f := Subtype.ext ht
      refine ⟨(c * (p : C)⁻¹) • P.inclT t, ?_⟩
      rw [map_smul, P.alC_inclT, h3, map_smul, ← algebraMap_smul C (p : O), map_natCast, smul_smul,
        inv_mul_cancel_right₀ h0, Point.inclOm, TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul,
        _root_.mul_one]
  refine ⟨hs, fun n x hx => LinearIndependent.of_comp P.pairV ?_⟩
  have e : (⇑P.pairV ∘ fun j => P.bLie (x j)) = ⇑P.alC.dualMap ∘ fun j => evLie P (x j) :=
    funext fun j => LinearMap.ext fun w => pairV_bLie_eq_evLie (x j) w
  rw [e]
  exact hx.map' _ (LinearMap.ker_eq_bot.2 (LinearMap.dualMap_injective_of_surjective hs))

end GlobalTheory.CompHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
section
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.NormUniq

variable {D : D7}

theorem wd_smul (T : Tor D) {N N' : ℕ} (x : VC D N N') (c : ℂ) (G : VC D N N' → ℂ) :
    Wd D T x (c • G) = c • Wd D T x G := by
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul]
  ring

theorem wd_add (T : Tor D) {N N' : ℕ} (x : VC D N N') (G G' : VC D N N' → ℂ) :
    Wd D T x (G + G') = Wd D T x G + Wd D T x G' := by
  funext z
  simp only [Wd, U, Pi.add_apply]
  ring

theorem applyAt0_smul {N N' : ℕ} (P : MvPolynomial (GL3Theta.Idx D N N') ℂ) {c : ℂ} (hc : c ≠ 0)
    (G : VC D N N' → ℂ) : GL3Theta.applyAt0 D P (c • G) = c * GL3Theta.applyAt0 D P G := by
  simp only [GL3Theta.applyAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have : TaylorLogMetric.taylor D (c • G) α = c * TaylorLogMetric.taylor D G α := by
    unfold TaylorLogMetric.taylor
    let g : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := ℂ) (G := ℂˣ) (Units.mk0 c hc)
    have e : c • G = ⇑g ∘ G := by
      funext z; simp [g, ContinuousLinearEquiv.smulLeft, Units.smul_def]
    rw [e, ContinuousLinearEquiv.iteratedFDeriv_comp_left]
    simp [g, ContinuousLinearEquiv.smulLeft, Units.smul_def]
    ring
  rw [this]; ring

theorem tt_zero (T : Tor D) {N N' : ℕ} : (0 : VC D N N' → ℂ) ∈ TT D T N N' :=
  ⟨differentiable_const 0, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩

theorem tt_add {T : Tor D} {N N' : ℕ} {F F' : VC D N N' → ℂ} (hF : F ∈ TT D T N N') (hF' : F' ∈ TT D T N N') :
    F + F' ∈ TT D T N N' := by
  obtain ⟨h1, m, hm, h2⟩ := hF
  obtain ⟨h1', m', hm', h2'⟩ := hF'
  refine ⟨h1.add h1', m * m', Nat.mul_pos hm hm', fun x hx => ?_⟩
  have e1 := h2 (m' • x) (AddSubgroup.nsmul_mem _ hx _)
  have e2 := h2' (m • x) (AddSubgroup.nsmul_mem _ hx _)
  rw [smul_smul] at e1 e2
  rw [mul_comm m' m] at e2
  rw [wd_add, e1, e2]

theorem tt_smul {T : Tor D} {N N' : ℕ} {F : VC D N N' → ℂ} (hF : F ∈ TT D T N N') (c : ℂ) :
    c • F ∈ TT D T N N' := by
  obtain ⟨h1, m, hm, h2⟩ := hF
  exact ⟨h1.const_smul c, m, hm, fun x hx => by rw [wd_smul, h2 x hx]⟩

theorem tt_sum {T : Tor D} {N N' : ℕ} {ι : Type*} (s : Finset ι) {F : ι → VC D N N' → ℂ}
    (hF : ∀ i ∈ s, F i ∈ TT D T N N') : ∑ i ∈ s, F i ∈ TT D T N N' := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tt_zero T
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact tt_add (hF a (Finset.mem_insert_self a s)) (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

end GlobalTheory.FunObj.NormUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelCharacterEqProdSuperdiagonalSum
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
open GlobalTheory.LevPull (CongMod)
open scoped TensorProduct Matrix
noncomputable section

namespace GlobalTheory.TypeBase

def piCongrLeftMul {α β : Type} (P : β → Type) [∀ b, Mul (P b)] (e : α ≃ β) : (∀ a, P (e a)) ≃* ∀ b, P b :=
  { Equiv.piCongrLeft P e with
    map_mul' := fun f g => by
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      simp only [Equiv.toFun_as_coe, Pi.mul_apply, Equiv.piCongrLeft_apply_apply] }

theorem piCongrLeftMul_apply {α β : Type} (P : β → Type) [∀ b, Mul (P b)] (e : α ≃ β) (f : ∀ a, P (e a)) (a : α) :
    piCongrLeftMul P e f (e a) = f a :=
  Equiv.piCongrLeft_apply_apply P e f a

def bcEquiv {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (f : A ≃+* B) :
    GL n A ≃* GL n B :=
  MonoidHom.toMulEquiv (Formalism.UG.bc (f : A →+* B)) (Formalism.UG.bc (f.symm : B →+* A))
    (by ext g i j; simp [Formalism.UG.bc]) (by ext g i j; simp [Formalism.UG.bc])

theorem bc_apply {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (f : A →+* B)
    (g : GL n A) (i j : n) : ((Formalism.UG.bc f g : GL n B) : Matrix n n B) i j = f ((g : Matrix n n A) i j) := rfl

theorem bc_mem_unip_iff {A B : Type} [Field A] [CommRing B] {r : ℕ} (f : A ≃+* B) (g : GL (Fin r) A) :
    Formalism.UG.bc (f : A →+* B) g ∈ unip B r ↔ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.unitri r A := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have h := h1 (show j.val < i.val from hij)
      rw [bc_apply] at h
      exact f.injective (h.trans (map_zero f).symm)
    · have h := h2 i
      rw [bc_apply] at h
      exact f.injective (h.trans (map_one f).symm)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [bc_apply, h1 (show id j < id i from hij), map_zero]
    · rw [bc_apply, h2 i, map_one]

theorem edgeSum_bc {A B : Type} [Field A] [CommRing B] {r : ℕ} (f : A →+* B) (g : GL (Fin r) A) :
    edgeSum supEdge (Formalism.UG.bc f g) = f (GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.superDiag (g : Matrix (Fin r) (Fin r) A)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [edgeSum, GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.superDiag, supEdge, bc_apply, map_sum, apply_ite f, map_zero]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr

theorem det_unip {κ : Type} [CommRing κ] {r : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unip κ r) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
    Matrix.det_of_upperTriangular (fun i j hij => hg.1 hij)]
  exact Finset.prod_eq_one fun i _ => hg.2 i

theorem exists_char {Ks : Type} [Field Ks] (σ : Ks →+* ℂ) (p : ℕ) [Fact p.Prime] {ζ : Ks} (hζ : IsPrimitiveRoot ζ p)
    {k : Type} [CommRing k] (f : ZMod p ≃+* k) (χ : AddChar k ℂ) :
    ∃ ψ : AddChar (ZMod p) Ks, ∀ x, σ (ψ x) = χ (f x) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hz : χ (f 1) ^ p = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, ← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero,
      AddChar.map_zero_eq_one]
  obtain ⟨k, -, hk⟩ := (hζ.map_of_injective σ.injective).eq_pow_of_pow_eq_one hz
  have hc : (ζ ^ k) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨AddChar.zmodChar p hc, fun x => ?_⟩
  rw [AddChar.zmodChar_apply, map_pow, map_pow, hk, ← AddChar.map_nsmul_eq_pow, ← map_nsmul, nsmul_eq_mul, mul_one,
    ZMod.natCast_zmod_val]

theorem baseLevelCharacter_eq_prod_superdiagonalSum {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) ℂ) (g) (hg : g ∈ (P0 Pg r ψ).H) :
    (((P0 Pg r ψ).chi ⟨g, hg⟩ : ℂˣ) : ℂ) = ∏ PP : Pg, ψ PP.1 (edgeSum supEdge (g PP)) := by
  unfold P0 LevelP.ofLocal
  dsimp only
  letI : IsOneApply ((Subgroup.pi Set.univ (fun PP : Pg => unip (kP PP.1) r)) →* ℂˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply ((Subgroup.pi Set.univ (fun PP : Pg => unip (kP PP.1) r)) →* ℂˣ) := ⟨fun _ _ _ => rfl⟩
  rw [prod_apply, Units.coe_prod]
  rfl

theorem mem_lastZeroOrthImageSubspace_iff {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) (g : G0 Pg r) :
    g ∈ (P0 Pg r ψ).H ↔ ∀ PP, g PP ∈ unip (kP PP.1) r := by
  simp [P0, LevelP.ofLocal, Subgroup.mem_pi]

end GlobalTheory.TypeBase

namespace GlobalTheory.TypeBase

theorem base_level_unip_char : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_levels F → R.grp_chiW → (∀ k, ∃ ζ : Ks, IsPrimitiveRoot ζ (D.host.g k)) → ∀ (e : Sq D.host ≃ R.Pg) (iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1), ∃ (t : LevelGroup D.host ≃* G) (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) Ks), (∀ u v, R.eG (t u) (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (u v)) ∧ (∀ v, ψ v ≠ 1) ∧ (∀ u, t u ∈ (F.lvl false).P ↔ u ∈ levelU D.host) ∧ ∀ u (h : t u ∈ (F.lvl false).P), algebraMap Ks D.what₂.LL (psiU ψ u) = ((F.lvl false).ψ ⟨t u, h⟩ : D.what₂.LLˣ) ∧ ∀ i, (R.FW i).chi (t u) = 1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hlevels hchiW hζ e iso
  obtain ⟨ψ0, hgen, hlev, -⟩ := hlevels
  let φ : LevelGroup D.host ≃* G0 R.Pg D.R.r :=
    (MulEquiv.piCongrRight fun v : Sq D.host => (bcEquiv (n := Fin D.R.r) (iso v))).trans
      (piCongrLeftMul (fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) e)
  have hφ : ∀ u v, φ u (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (u v) := fun u v =>
    piCongrLeftMul_apply (fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) e
      (fun v => Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (u v)) v
  have hex : ∀ v : Sq D.host, ∃ ψ : AddChar (ZMod (D.host.g v.1)) Ks,
      ∀ x, D.what₂.embLL (algebraMap Ks D.what₂.LL (ψ x)) = ψ0 (e v).1 (iso v x) := by
    intro v
    obtain ⟨ζ, hz⟩ := hζ v.1
    exact exists_char (D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)) _ hz (iso v) (ψ0 (e v).1)
  choose ψ hψ using hex
  refine ⟨φ.trans R.eG.symm, ψ, fun u v => ?_, fun v h1 => ?_, fun u => ?_, fun u h => ?_⟩
  · show R.eG (R.eG.symm (φ u)) (e v) = _
    rw [MulEquiv.apply_symm_apply, hφ]
  · apply hgen (e v).1 (e v).2
    ext y
    obtain ⟨x, rfl⟩ := (iso v).surjective y
    rw [← hψ v x, h1, AddChar.one_apply, map_one, map_one, AddChar.one_apply]
  · show φ u ∈ (R.levR F false).H ↔ _
    rw [hlev, mem_lastZeroOrthImageSubspace_iff, GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.levelU, Subgroup.mem_pi]
    simp only [Set.mem_univ, true_implies]
    exact (e.forall_congr fun v => by rw [hφ, bc_mem_unip_iff]).symm
  · have hm : φ u ∈ (P0 R.Pg D.R.r ψ0).H := by rw [← hlev]; exact h
    have hun : ∀ PP, φ u PP ∈ unip (kP PP.1) D.R.r := (mem_lastZeroOrthImageSubspace_iff _ _ _ _).1 hm
    refine ⟨?_, fun i => ?_⟩
    · apply D.what₂.embLL.injective
      have e1 : (R.levR F false).chi ⟨φ u, h⟩ =
          Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((F.lvl false).ψ ⟨(φ.trans R.eG.symm) u, h⟩) := rfl
      have key : ∀ X : LevelP R.Pg D.R.r ℂ, X = P0 R.Pg D.R.r ψ0 → ∀ g (hg : g ∈ X.H),
          ((X.chi ⟨g, hg⟩ : ℂˣ) : ℂ) = ∏ PP : R.Pg, ψ0 PP.1 (edgeSum supEdge (g PP)) := by
        rintro X rfl g hg
        exact baseLevelCharacter_eq_prod_superdiagonalSum _ _ _ g hg
      have h2 := key _ hlev (φ u) h
      rw [e1, Units.coe_map] at h2
      rw [show D.what₂.embLL (((F.lvl false).ψ ⟨(φ.trans R.eG.symm) u, h⟩ : D.what₂.LLˣ) : D.what₂.LL) =
        ∏ PP : R.Pg, ψ0 PP.1 (edgeSum supEdge (φ u PP)) from h2]
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.psiU, map_prod]
      refine Finset.prod_equiv e (by simp) fun v _ => ?_
      rw [hψ, hφ, edgeSum_bc, RingEquiv.coe_toRingHom]
    · apply Units.ext
      apply D.what₂.embLL.injective
      have hg : R.eG ((φ.trans R.eG.symm) u) = φ u := R.eG.apply_symm_apply _
      rw [hchiW i, hg, Finset.prod_eq_one (fun PP _ => by rw [det_unip (hun PP), map_one, Units.val_one]),
        Units.val_one, map_one]

end GlobalTheory.TypeBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniNumberFieldOfHilbertSamuel
section
set_option autoImplicit false

namespace GlobalTheory.HSShort

theorem bertiniNF_of_bertini (h : Bertini) : BertiniNF := by
  intro F _ _ T hg hb δ f hf
  obtain ⟨hδ, Q, hQ, hs⟩ := h F T hg hb δ f hf
  exact ⟨hδ, Q, hQ, fun E _ _ _ s hsQ => hs E s hsQ⟩

theorem bertiniNumberField_of_hilbertSamuel : GlobalTheory.HSCore.Quoted → BertiniNF :=
  fun hq => bertiniNF_of_bertini (_root_.GlobalTheory.BertiniTop.bertini hq)

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLink

variable {D : D7} {m n : ℕ}

abbrev cAl (D : D7) : AE D →ₐ[AF D.host.F] AE D := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig

abbrev UD (D : D7) {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) : Type := UA D.sp.cm.sig J

theorem cAl_eq (z : AE D) : cAl D z = cA D z := GlobalTheory.IwLine.cA_eq_sigR _ z

variable {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* StdUnn.G D n}

section Witt

variable {J : Matrix (Fin n) (Fin n) D.host.E}

theorem trA_cA (z : AE D) : StdUnn.trA (cA D z) = StdUnn.trA z := by
  let e : AE D ≃ₐ[AF D.host.F] AE D := AlgEquiv.ofAlgHom (cAl D) (cAl D)
    (AlgHom.ext fun z => by simp only [AlgHom.comp_apply, cAl_eq, cA_cA, AlgHom.id_apply])
    (AlgHom.ext fun z => by simp only [AlgHom.comp_apply, cAl_eq, cA_cA, AlgHom.id_apply])
  rw [← cAl_eq]
  exact Algebra.trace_eq_of_algEquiv e z

theorem trA_inner_comm (V : HSp D) (x y : Mx D V.rank n) :
    StdUnn.trA (Matrix.trace (StdUnn.inner V x y)) = StdUnn.trA (Matrix.trace (StdUnn.inner V y x)) := by
  rw [← trA_cA, ← trace_adj, StdUnn.inner, StdUnn.inner, adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

end Witt

end GlobalTheory.SWLink

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BotPairSmall

def cvec (D : D7) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (o a d : ℕ) (e0 : VC D a d → ℂ) : VC D a d → ℂ :=
  ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d))
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)

def blockSet (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : Set (GA D N) :=
  {h | h ∈ intG D N ∧ ∀ i j : Fin N, j.1 < a → a ≤ i.1 →
    ((h : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪}

def blockJ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : Subgroup (GA D N) := Subgroup.closure (blockSet D 𝔪 a N)

theorem blockJ_le (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a N : ℕ) : blockJ D 𝔪 a N ≤ intG D N :=
  (Subgroup.closure_le _).2 fun _ h => h.1

theorem conj_smul_ne_bot (D : D7) {𝔪 : Ideal (𝓞 D.host.E)} (h : 𝔪 ≠ ⊥) : D.host.conj • 𝔪 ≠ ⊥ := by
  intro e
  apply h
  have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) e
  simpa [smul_smul] using this

end GlobalTheory.BotPairSmall
end
end

