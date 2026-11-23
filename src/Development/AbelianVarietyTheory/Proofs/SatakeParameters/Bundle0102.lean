module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0003
public import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.Bundle0002
public import Formalism.GaussJetBounds.GaussJetProofs.OrbMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.JetTdegEqDegree
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InstFintypeHodgeBidegree
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicUnitarySupportedAtFinitePlaceEqLocalUnitar
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.SuppLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem adele_ext {z z' : AF F ⊗[F] E} (h1 : infP F E z = infP F E z')
    (h2 : ∀ w, evF E w (finP F E z) = evF E w (finP F E z')) : z = z' := by
  have h3 : finP F E z = finP F E z' := evF_ext h2
  let b := Module.Basis.ofVectorSpace F E
  refine (Algebra.TensorProduct.basis (AF F) b).repr.injective (Finsupp.ext fun k => Prod.ext ?_ ?_)
  · have a1 := GlobalTheory.LatticeLocalGlobal.repr_map (fstA F) b z k
    have a2 := GlobalTheory.LatticeLocalGlobal.repr_map (fstA F) b z' k
    exact a1.symm.trans ((congrArg (fun x => (Algebra.TensorProduct.basis (Ainf F) b).repr x k) h1).trans a2)
  · have a1 := GlobalTheory.LatticeLocalGlobal.repr_map (sndA F) b z k
    have a2 := GlobalTheory.LatticeLocalGlobal.repr_map (sndA F) b z' k
    exact a1.symm.trans ((congrArg (fun x => (Algebra.TensorProduct.basis (Af F) b).repr x k) h3).trans a2)

theorem idem_mul_iff {v : HeightOneSpectrum (𝓞 F)} {e : AF F ⊗[F] E} (he : IsIdemOf E v e) (x : AF F ⊗[F] E) :
    e * x = x ↔ infP F E x = 0 ∧ ∀ w, w ≠ v → evF E w (finP F E x) = 0 := by
  obtain ⟨e1, e2, e3⟩ := he
  constructor
  · intro h
    refine ⟨?_, fun w hw => ?_⟩
    · rw [← h, map_mul, e1, zero_mul]
    · rw [← h, map_mul, map_mul, e3 w hw, zero_mul]
  · rintro ⟨h1, h2⟩
    refine adele_ext ?_ fun w => ?_
    · rw [map_mul, h1, mul_zero]
    · rw [map_mul, map_mul]
      by_cases hw : w = v
      · subst hw
        rw [e2, one_mul]
      · rw [h2 w hw, mul_zero]

theorem bc_eq_one_iff {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (φ : A →+* B) (g : GL (Fin n) A) :
    Formalism.UG.bc φ g = 1 ↔ ∀ i j, φ ((g.1 - 1) i j) = 0 := by
  rw [Units.ext_iff, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  show φ (g.1 i j) = (1 : Matrix (Fin n) (Fin n) B) i j ↔ _
  rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable [NumberField E] [StarRing E] (hc : CMData F E) (V : HSpace E)

theorem supp_iff {v : HeightOneSpectrum (𝓞 F)} {e : AF F ⊗[F] E} (he : IsIdemOf E v e)
    (g : HA (AF F) hc.sig V.gram) :
    Supp hc V e g ↔ IsFin hc V g ∧ ∀ w, w ≠ v → locMat hc V w g = 1 := by
  have h1 : IsFin hc V g ↔ ∀ i j, infP F E (((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j) = 0 :=
    bc_eq_one_iff _ _
  have h2 : ∀ w, locMat hc V w g = 1 ↔
      ∀ i j, evF E w (finP F E (((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j)) = 0 :=
    fun w => bc_eq_one_iff ((evF E w).comp (finP F E)) (HA.mat (AF F) hc.sig V.gram g)
  rw [h1]
  simp only [h2, Supp, idem_mul_iff he]
  exact ⟨fun h => ⟨fun i j => (h i j).1, fun w hw i j => (h i j).2 w hw⟩,
    fun h i j => ⟨h.1 i j, fun w hw => h.2 w hw i j⟩⟩

theorem supp_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E), IsIdemOf E v e → (∀ g, Supp hc V e g ↔ IsFin hc V g ∧ ∀ w, w ≠ v → locMat hc V w g = 1) ∧ (∀ g g', Supp hc V e g → Supp hc V e g' → locMat hc V v g = locMat hc V v g' → g = g') ∧ ∀ u ∈ HR (Fv F v) hc.sig V.gram, ∃ g, Supp hc V e g ∧ locMat hc V v g = u := by
  classical
  intro F E _ _ _ _ _ _ hc V v e he
  refine ⟨supp_iff hc V he, fun g g' hg hg' h => ?_, fun u hu => ?_⟩
  · obtain ⟨a1, a2⟩ := (supp_iff hc V he g).1 hg
    obtain ⟨b1, b2⟩ := (supp_iff hc V he g').1 hg'
    have hw : ∀ w, locMat hc V w g = locMat hc V w g' := fun w => by
      by_cases hw : w = v
      · exact hw ▸ h
      · rw [a2 w hw, b2 w hw]
    have hi := Eq.trans a1 (Eq.symm b1)
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => adele_ext ?_ fun w => ?_))
    · exact congrArg (fun x => x.1 i j) hi
    · exact congrArg (fun x => x.1 i j) (hw w)
  · let u' : HA (Fv F v) hc.sig V.gram := ⟨u, hu⟩
    obtain ⟨k, hk⟩ := GlobalTheory.LocalUnitaryGlue.exists_of_finite hc.sig V.gram
      (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => HA (Fv F w) hc.sig V.gram) v u')
      ((Set.finite_singleton v).subset fun w hw => by
        by_contra hne
        exact hw (Pi.mulSingle_eq_of_ne
          (M := fun w : HeightOneSpectrum (𝓞 F) => HA (Fv F w) hc.sig V.gram) (i := v) (i' := w) hne u'))
    have hl : ∀ w, locMat hc V w (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ofFin hc V k) = HA.mat _ _ _
        (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => HA (Fv F w) hc.sig V.gram) v u' w) := fun w => by
      rw [← hk w]
      exact congrArg (fun x => HA.mat _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projLoc hc V w x))
        (GlobalTheory.AutFunCompare.projFin_ofFin hc V k)
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ofFin hc V k, (supp_iff hc V he _).2 ⟨?_, fun w hw => ?_⟩, ?_⟩
    · exact congrArg (HA.mat _ _ _) (GlobalTheory.AutFunCompare.projInf_ofFin hc V k)
    · rw [hl, Pi.mulSingle_eq_of_ne hw]; rfl
    · rw [hl, Pi.mulSingle_eq_same]; rfl

end GlobalTheory.SuppLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardCosetsEqSubspacesKernelResidue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke.Cosets

open IsLocalRing

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {p : O}

theorem map_res_eq_zero_iff (hp : Irreducible p) {m n : ℕ} (X : Matrix (Fin m) (Fin n) O) :
    X.map (residue O) = 0 ↔ ∃ C : Matrix (Fin m) (Fin n) O, X = p • C := by
  have hm : maximalIdeal O = Ideal.span {p} := hp.maximalIdeal_eq
  constructor
  · intro h
    have : ∀ i j, ∃ c, X i j = p * c := by
      intro i j
      have h1 : residue O (X i j) = 0 := congrFun (congrFun h i) j
      rw [residue_eq_zero_iff, hm, Ideal.mem_span_singleton] at h1
      exact h1
    choose C hC using this
    exact ⟨Matrix.of C, Matrix.ext hC⟩
  · rintro ⟨C, rfl⟩
    ext i j
    have : residue O (p * C i j) = 0 := by
      rw [residue_eq_zero_iff, hm, Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
    exact this

theorem map_inj {m n : ℕ} {X Y : Matrix (Fin m) (Fin n) O}
    (h : X.map (algebraMap O K) = Y.map (algebraMap O K)) : X = Y := by
  ext i j
  exact IsFractionRing.injective O K (congrFun (congrFun h i) j)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem map_smul' {m n : ℕ} (c : O) (X : Matrix (Fin m) (Fin n) O) :
    (c • X).map (algebraMap O K) = algebraMap O K c • X.map (algebraMap O K) := by
  ext i j
  simp

theorem intM_inv_smul_iff (hp : Irreducible p) {m n : ℕ} (X : Matrix (Fin m) (Fin n) O) :
    IntM O ((algebraMap O K p)⁻¹ • X.map (algebraMap O K)) ↔ X.map (residue O) = 0 := by
  have h0 : algebraMap O K p ≠ 0 := by
    intro h
    exact hp.ne_zero (IsFractionRing.injective O K (by rw [h, map_zero]))
  rw [map_res_eq_zero_iff hp, intM_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, map_inj (K := K) ?_⟩
    rw [map_smul', hC, smul_smul, mul_inv_cancel₀ h0, one_smul]
  · rintro ⟨C, rfl⟩
    refine ⟨C, ?_⟩
    rw [map_smul', smul_smul, inv_mul_cancel₀ h0, one_smul]

theorem exists_of_range_le (hp : Irreducible p) {n : ℕ} {A A' : Matrix (Fin n) (Fin n) O}
    (h : LinearMap.range (A'.map (residue O)).mulVecLin ≤ LinearMap.range (A.map (residue O)).mulVecLin) :
    ∃ B C : Matrix (Fin n) (Fin n) O, A' = A * B + p • C := by
  have h1 : ∀ j, ∃ b : Fin n → O, (A.map (residue O)) *ᵥ (fun i => residue O (b i)) =
      (A'.map (residue O)) *ᵥ Pi.single j 1 := by
    intro j
    obtain ⟨y, hy⟩ := h ⟨Pi.single j 1, rfl⟩
    choose b hb using fun i => residue_surjective (R := O) (y i)
    refine ⟨b, ?_⟩
    have : (fun i => residue O (b i)) = y := funext hb
    rw [this]
    exact hy
  choose b hb using h1
  obtain ⟨C, hC⟩ := (map_res_eq_zero_iff hp (A' - A * Matrix.of fun i j => b j i)).1 (by
    ext i j
    have := congrFun (hb j) i
    rw [Matrix.mulVec_single_one] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.col_apply] at this
    simp [Matrix.mul_apply, ← this])
  exact ⟨_, C, by rw [← hC]; abel⟩

theorem range_le_of_mul {n : ℕ} {A A' : Matrix (Fin n) (Fin n) O} {a a' : GL (Fin n) K}
    (hA : A.map (algebraMap O K) = a.1) (hA' : A'.map (algebraMap O K) = a'.1) (h : IntM O (a⁻¹ * a').1) :
    LinearMap.range (A'.map (residue O)).mulVecLin ≤ LinearMap.range (A.map (residue O)).mulVecLin := by
  obtain ⟨B, hB⟩ := intM_iff.1 h
  have : A' = A * B := by
    refine map_inj (K := K) ?_
    rw [Matrix.map_mul, hA, hA', hB, ← Units.val_mul, mul_inv_cancel_left]
  rw [this, Matrix.map_mul, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

theorem intM_of_range_le (hp : Irreducible p) {n : ℕ} {A A' : Matrix (Fin n) (Fin n) O} {a a' : GL (Fin n) K}
    (hA : A.map (algebraMap O K) = a.1) (hA' : A'.map (algebraMap O K) = a'.1)
    (ha : IntM O (algebraMap O K p • (a⁻¹).1))
    (h : LinearMap.range (A'.map (residue O)).mulVecLin ≤ LinearMap.range (A.map (residue O)).mulVecLin) :
    IntM O (a⁻¹ * a').1 := by
  obtain ⟨B, C, hBC⟩ := exists_of_range_le hp h
  have : (a⁻¹ * a').1 = B.map (algebraMap O K) + (algebraMap O K p • (a⁻¹).1) * C.map (algebraMap O K) := by
    rw [Units.val_mul, ← hA', hBC, Matrix.map_add _ (map_add _), Matrix.map_mul, map_smul', hA, Matrix.mul_add,
      ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [this]
  exact (intM_iff.2 ⟨B, rfl⟩).add (ha.mul (intM_iff.2 ⟨C, rfl⟩))

theorem GInt.exists_det {n : ℕ} {k : GL (Fin n) K} (hk : GInt O k) : ∃ u : Oˣ, k.1.det = algebraMap O K u := by
  obtain ⟨A, hA⟩ := intM_iff.1 hk.1
  obtain ⟨B, hB⟩ := intM_iff.1 hk.2
  have : A * B = 1 := by
    refine map_inj (K := K) ?_
    rw [Matrix.map_mul, hA, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hu : IsUnit A.det := Matrix.isUnit_det_of_right_inverse this
  refine ⟨hu.unit, ?_⟩
  rw [← hA, IsUnit.unit_spec, RingHom.map_det]
  rfl

theorem hk_mul {n j : ℕ} {α k₁ k₂ : GL (Fin n) K} (hα : Hk O p j α) (h₁ : GInt O k₁) (h₂ : GInt O k₂) :
    Hk O p j (k₁ * α * k₂) := by
  refine ⟨(h₁.1.mul hα.1).mul h₂.1, ?_, ?_⟩
  · have := (h₂.2.mul hα.2.1).mul h₁.2
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
    rwa [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] at this
  · obtain ⟨u, hu⟩ := hα.2.2
    obtain ⟨u₁, hu₁⟩ := GInt.exists_det h₁
    obtain ⟨u₂, hu₂⟩ := GInt.exists_det h₂
    refine ⟨u₁ * u * u₂, ?_⟩
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hu, hu₁, hu₂, ← map_mul, ← map_mul]
    congr 1
    push_cast
    ring

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem gInt_map {n : ℕ} (g : GL (Fin n) O) : GInt O (Matrix.GeneralLinearGroup.map (algebraMap O K) g) :=
  ⟨intM_iff.2 ⟨g.1, rfl⟩, by rw [← map_inv]; exact intM_iff.2 ⟨(g⁻¹).1, rfl⟩⟩

theorem cond_iff (hp : Irreducible p) {m n : ℕ} (z : Matrix (Fin m) (Fin n) O) {A : Matrix (Fin n) (Fin n) O}
    {a : Matrix (Fin n) (Fin n) K} (hA : A.map (algebraMap O K) = a) :
    IntM O (((algebraMap O K p)⁻¹ • z.map (algebraMap O K)) * a) ↔
      LinearMap.range (A.map (residue O)).mulVecLin ≤ LinearMap.ker (z.map (residue O)).mulVecLin := by
  rw [← hA, Matrix.smul_mul, ← Matrix.map_mul, intM_inv_smul_iff hp, LinearMap.range_le_ker_iff,
    ← Matrix.mulVecLin_mul, Matrix.map_mul]
  constructor
  · intro h
    rw [h, Matrix.mulVecLin_zero]
  · intro h
    apply Matrix.toLin'.injective
    rw [map_zero]
    exact h

theorem card_cosets : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (p : O), Irreducible p → ∀ (m n j : ℕ) (ι : Type) (α : GL (Fin n) K) (R : Finset ι) (ρ : ι → GL (Fin n) K) (z : Matrix (Fin m) (Fin n) O), j ≤ n → Hk O p j α → Reps O α R ρ → Nat.card {γ : ι // γ ∈ R ∧ IntM O (((algebraMap O K p)⁻¹ • z.map (algebraMap O K)) * (ρ γ).1)} = Nat.card {W : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O) // Module.finrank (IsLocalRing.ResidueField O) W + j = n ∧ W ≤ LinearMap.ker (z.map (IsLocalRing.residue O)).mulVecLin} := by
  intro O K _ _ _ _ _ _ p hp m n j ι α R ρ z hj hα hR
  have hH : ∀ γ ∈ R, Hk O p j (ρ γ) := by
    intro γ hγ
    obtain ⟨k₁, k₂, h₁, h₂, h⟩ := hR.1 γ hγ
    rw [h]
    exact hk_mul hα h₁ h₂
  choose A hA using fun γ (hγ : γ ∈ R) => intM_iff.1 (hH γ hγ).1
  refine Nat.card_eq_of_bijective (fun γ => ⟨LinearMap.range ((A γ.1 γ.2.1).map (residue O)).mulVecLin,
    GlobalTheory.SplitHecke.finrank_range_reduction O K p hp n j _ _ hj (hH _ γ.2.1) (hA _ γ.2.1), (cond_iff hp z (hA _ γ.2.1)).1 γ.2.2⟩) ⟨?_, ?_⟩
  · rintro ⟨γ, hγ, hγ1⟩ ⟨γ', hγ', hγ2⟩ h
    have h' : LinearMap.range ((A γ hγ).map (residue O)).mulVecLin =
        LinearMap.range ((A γ' hγ').map (residue O)).mulVecLin := congrArg Subtype.val h
    have hG : GInt O ((ρ γ)⁻¹ * ρ γ') := by
      refine ⟨intM_of_range_le hp (hA γ hγ) (hA γ' hγ') (hH γ hγ).2.1 h'.ge, ?_⟩
      rw [_root_.mul_inv_rev, inv_inv]
      exact intM_of_range_le hp (hA γ' hγ') (hA γ hγ) (hH γ' hγ').2.1 h'.le
    obtain ⟨k₁, k₂, h₁, h₂, he⟩ := hR.1 γ' hγ'
    have hu := hR.2 k₁ k₂ h₁ h₂
    rw [← he] at hu
    exact Subtype.ext (hu.unique ⟨hγ, hG⟩ ⟨hγ', by rw [inv_mul_cancel]; exact gInt_one⟩)
  · rintro ⟨W, hW, hWz⟩
    obtain ⟨A₀, hA₀⟩ := intM_iff.1 hα.1
    have h0 := GlobalTheory.SplitHecke.finrank_range_reduction O K p hp n j _ _ hj hα hA₀
    obtain ⟨g, hg⟩ := GlobalTheory.SplitHecke.exists_gl_map_residue_eq O n (LinearMap.range (A₀.map (residue O)).mulVecLin) W (by omega)
    obtain ⟨γ, ⟨hγ, hG⟩, -⟩ := hR.2 _ 1 (gInt_map g) gInt_one
    rw [mul_one] at hG
    have hgA : (g.1 * A₀).map (algebraMap O K) =
        (Matrix.GeneralLinearGroup.map (algebraMap O K) g * α).1 := by
      rw [Matrix.map_mul, hA₀]
      rfl
    have hr : LinearMap.range ((A γ hγ).map (residue O)).mulVecLin = W := by
      rw [← hg, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul, ← Matrix.map_mul]
      refine le_antisymm (range_le_of_mul hgA (hA γ hγ) ?_) (range_le_of_mul (hA γ hγ) hgA hG.1)
      have := hG.2
      rwa [_root_.mul_inv_rev, inv_inv] at this
    exact ⟨⟨γ, hγ, (cond_iff hp z (hA γ hγ)).2 (hr ▸ hWz)⟩, Subtype.ext hr⟩

end GlobalTheory.SplitHecke.Cosets
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralClopenDecompositionOfSmooth
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SmoothComponents

open Topology TopologicalSpace

theorem irreducibleComponent_eq_closure (Z : Scheme.{0})
    (hdom : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) {C : Set Z} (hC : C ∈ irreducibleComponents Z)
    {x : Z} (hx : x ∈ C) :
    haveI := hdom x
    C = closure {Z.fromSpecStalk x (genericPoint (Spec (Z.presheaf.stalk x)))} := by
  haveI := hdom x
  set ξ := Z.fromSpecStalk x (genericPoint (Spec (Z.presheaf.stalk x)))
  have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hgen : IsGenericPoint hC.1.genericPoint C := by
    simpa [hCc.closure_eq] using hC.1.isGenericPoint_genericPoint_closure
  have hηx : hC.1.genericPoint ⤳ x := hgen.specializes hx
  have hmem : hC.1.genericPoint ∈ Set.range (Z.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hηx
  obtain ⟨p, hp⟩ := hmem
  have hξη : ξ ⤳ hC.1.genericPoint := by
    rw [← hp]
    exact ((genericPoint_spec (Spec (Z.presheaf.stalk x))).specializes trivial).map
      (Z.fromSpecStalk x).continuous
  have hsub : C ⊆ closure {ξ} := by
    rw [← hgen.def]
    exact closure_minimal (by simpa using specializes_iff_mem_closure.mp hξη) isClosed_closure
  have hirr : IsIrreducible (closure {ξ}) := isIrreducible_singleton.closure
  exact le_antisymm hsub (hC.2 hirr hsub)

end GlobalTheory.SmoothComponents

namespace GlobalTheory.SmoothComponents

open Topology TopologicalSpace

theorem main : ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s]
    [CompactSpace Z], ∃ (J : Type) (_ : Fintype J) (V : J → Z.Opens),
      (∀ i j, i ≠ j → V i ⊓ V j = ⊥) ∧ iSup V = ⊤ ∧ ∀ j, IsIntegral (V j).toScheme := by
  intro Z s d _ _
  have hs : Smooth s := SmoothOfRelativeDimension.smooth d s
  obtain ⟨hred, -, hln⟩ :=
    isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Z s hs
  have hdom : ∀ x : Z, IsDomain (Z.presheaf.stalk x) := fun x ↦
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth s
      (isDomain_and_isIntegrallyClosed_stalk_Sp ℂ) x).1
  haveI : IsNoetherian Z := ⟨⟩
  have hfin : (irreducibleComponents Z).Finite := finite_irreducibleComponents_of_isNoetherian
  have disj : ∀ C ∈ irreducibleComponents Z, ∀ D ∈ irreducibleComponents Z, C ≠ D →
      Disjoint C D := by
    intro C hC D hD hne
    rw [Set.disjoint_left]
    intro x hxC hxD
    exact hne ((irreducibleComponent_eq_closure Z hdom hC hxC).trans
      (irreducibleComponent_eq_closure Z hdom hD hxD).symm)
  have cover : ∀ x : Z, ∃ C ∈ irreducibleComponents Z, x ∈ C := fun x ↦
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x,
      mem_irreducibleComponent⟩
  have hopen : ∀ C ∈ irreducibleComponents Z, IsOpen C := by
    intro C hC
    have hc : Cᶜ = ⋃ D ∈ irreducibleComponents Z \ {C}, D := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff,
        exists_prop]
      constructor
      · intro hx
        obtain ⟨D, hD, hxD⟩ := cover x
        exact ⟨D, ⟨hD, fun h ↦ hx (h ▸ hxD)⟩, hxD⟩
      · rintro ⟨D, ⟨hD, hne⟩, hxD⟩ hxC
        exact Set.disjoint_left.mp (disj D hD C hC hne) hxD hxC
    rw [← isClosed_compl_iff, hc]
    exact (hfin.subset Set.diff_subset).isClosed_biUnion fun D hD ↦ isClosed_of_mem_irreducibleComponents D hD.1
  letI : Fintype (irreducibleComponents Z) := hfin.fintype
  refine ⟨irreducibleComponents Z, inferInstance, fun C ↦ ⟨C.1, hopen C.1 C.2⟩, ?_, ?_, ?_⟩
  · intro i j hij
    apply Opens.ext
    simp only [Opens.coe_inf, Opens.coe_bot]
    exact Set.disjoint_iff_inter_eq_empty.mp (disj i.1 i.2 j.1 j.2 fun h ↦ hij (Subtype.ext h))
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    rw [Opens.mem_iSup]
    obtain ⟨C, hC, hxC⟩ := cover x
    exact ⟨⟨C, hC⟩, hxC⟩
  · intro C
    have hirr : IsIrreducible C.1 := C.2.1
    haveI : IrreducibleSpace (C.1 : Set Z) := Subtype.irreducibleSpace hirr
    let U : Z.Opens := ⟨C.1, hopen C.1 C.2⟩
    change IsIntegral U.toScheme
    haveI : IrreducibleSpace U.toScheme := this
    exact isIntegral_of_irreducibleSpace_of_isReduced _

end GlobalTheory.SmoothComponents
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExpFactorAllOrbitsEqProdOrbitsStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expFactor_allOrbits_eq_prod_orbits : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (R : Finset (OrbitPlaces.Pl D)) {M N N' : ℕ} (eA : Fin M ≃ R × Fin N)
    (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hbe : constantCoeff be = 0), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (mvExp ((-1 : ℂ_[p]) • Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be)) =
      product_zeroth_first_parts.expS ℂ_[p] (OrbitPlaces.beAll D p (N0 := N) (N1 := N') R (fun _ => -1) (fun _ => be)) := by
  first | exact @GlobalTheory.ExpFacOrbits.expFactor_allOrbits | exact GlobalTheory.ExpFacOrbits.expFactor_allOrbits | (intros; apply GlobalTheory.ExpFacOrbits.expFactor_allOrbits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankReductionRangeAddCorankStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_reduction_range_add_corank : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (p : O), Irreducible p → ∀ (n j : ℕ) (a : GL (Fin n) K) (A : Matrix (Fin n) (Fin n) O), j ≤ n → Hk O p j a → A.map (algebraMap O K) = a.1 → Module.finrank (IsLocalRing.ResidueField O) (LinearMap.range (A.map (IsLocalRing.residue O)).mulVecLin) + j = n := by
  first | exact @GlobalTheory.SplitHecke.finrank_range_reduction | exact GlobalTheory.SplitHecke.finrank_range_reduction | (intros; apply GlobalTheory.SplitHecke.finrank_range_reduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeElementComponentMemStandardDoubleCosetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeElement_component_mem_standardDoubleCoset : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ (ϖ : D.host.E) (p : Ov D v) (k : ℕ) (α : GA D V), algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D ϖ) → IsHeckeElt V e ϖ k α → Hk (Ov D v) p k (rho V π β α) := by
  first | exact @GlobalTheory.SplitHecke.HeckeComp.hk_of_isHeckeElt | exact GlobalTheory.SplitHecke.HeckeComp.hk_of_isHeckeElt | (intros; apply GlobalTheory.SplitHecke.HeckeComp.hk_of_isHeckeElt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFiniteQCOmega
section
open CategoryTheory AlgebraicGeometry Module ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeFin

open GlobalTheory.CechDR GlobalTheory.QCoh

variable {k : Type} [Field k] {X : Scheme.{0}} (s : X ⟶ Sp k)

theorem finiteType_sec [LocallyOfFiniteType s] {U : X.Opens} (hU : IsAffineOpen U) :
    Algebra.FiniteType k (Sec s U) := by
  have h1 := LocallyOfFiniteType.finiteType_appLE s (isAffineOpen_top (Sp k)) hU
    (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact h1.comp h2

end GlobalTheory.HodgeFin
end
end

