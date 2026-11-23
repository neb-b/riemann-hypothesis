module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.RowLat
public import Formalism.PieriBlockIdeals.PieriColumnMinors.ProdInitialMinorsMemDetSpan
public import Formalism.LocalToGlobal.Columns.Bundle0011
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemClosureIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelDataX
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
section
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

def twistSpan (ν β : kˣ →* ℂˣ) : Submodule ℂ (Matrix A D k → ℂ) :=
  Submodule.span ℂ {z | ∃ (g : GL A k) (Ψ : Matrix A D k → ℂ), Ψ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧
    z = omA ν β g 1 Ψ - Ψ}

def lowRank (r : ℕ) : Submodule ℂ (Matrix A D k → ℂ) where
  carrier := {Φ | Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧ ∀ Y : Matrix A D k, Y.rank < r → Φ Y = 0}
  add_mem' hΦ hΨ := ⟨add_mem hΦ.1 hΨ.1, fun Y hY => by simp [hΦ.2 Y hY, hΨ.2 Y hY]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ hΦ := ⟨Submodule.smul_mem _ c hΦ.1, fun Y hY => by simp [hΦ.2 Y hY]⟩

theorem mem_lowRank {r : ℕ} {Φ : Matrix A D k → ℂ} :
    Φ ∈ lowRank r ↔ Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧ ∀ Y : Matrix A D k, Y.rank < r → Φ Y = 0 := Iff.rfl

theorem omA_one_apply (ν β : kˣ →* ℂˣ) (g : GL A k) (Φ : Matrix A D k → ℂ) (X : Matrix A D k) :
    omA ν β g 1 Φ X = (((ν (gdet g))⁻¹ : ℂˣ) : ℂ) * apow (gdet g) (-(Fintype.card D : ℂ) / 2) *
      Φ ((g⁻¹).val * X) := by
  simp [omA, invT_val]

theorem sub_mem_twistSpan (ν β : kˣ →* ℂˣ) (g : GL A k) {Ψ : Matrix A D k → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.WeilM.SB (Matrix A D k)) : omA ν β g 1 Ψ - Ψ ∈ twistSpan ν β :=
  Submodule.subset_span ⟨g, Ψ, hΨ, rfl⟩

def box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : Set (Matrix A D k) :=
  {X | ∀ i j, valuation k (X i j - C i j) ≤ valuation k ((ϖ ^ e i : kˣ) : k)}

def boxFn (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : Matrix A D k → ℂ := (box ϖ C e).indicator 1


omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
theorem box_eq_preimage (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    box ϖ C e = (fun X : Matrix A D k => Matrix.of fun i j => (((ϖ ^ e i)⁻¹ : kˣ) : k) * (X i j - C i j)) ⁻¹'
      {Y | ∀ i j, Y i j ∈ 𝒪[k]} := by
  ext X
  simp only [box, Set.mem_setOf_eq, Set.mem_preimage, of_apply, Valuation.mem_integer_iff, map_mul]
  refine forall₂_congr fun i j => ?_
  have h0 : 0 < valuation k ((ϖ ^ e i : kˣ) : k) := zero_lt_iff.2 (by simp)
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]


omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
theorem box_eq_image (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    box ϖ C e = (fun Y : Matrix A D k => Matrix.of fun i j => C i j + ((ϖ ^ e i : kˣ) : k) * Y i j) ''
      {Y | ∀ i j, Y i j ∈ 𝒪[k]} := by
  rw [box_eq_preimage]
  ext X
  constructor
  · intro hX
    refine ⟨_, hX, ?_⟩
    ext i j
    simp [← mul_assoc]
  · rintro ⟨Y, hY, rfl⟩
    simpa [← mul_assoc] using hY


omit [DecidableEq A] [DecidableEq D] in
theorem isCompact_box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : IsCompact (box ϖ C e) := by
  rw [box_eq_image]
  exact isCompact_intMatrix.image (by fun_prop)


omit [DecidableEq A] [DecidableEq D] in
theorem isClopen_box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : IsClopen (box ϖ C e) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : T2Space (Matrix A D k) := inferInstanceAs (T2Space (A → D → k))
  refine ⟨(isCompact_box ϖ C e).isClosed, ?_⟩
  rw [box_eq_preimage]
  exact isOpen_intMatrix.preimage (by fun_prop)


omit [DecidableEq A] [DecidableEq D] in
theorem boxFn_mem_SB (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    boxFn ϖ C e ∈ GlobalTheory.WeilM.SB (Matrix A D k) :=
  ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) (isClopen_box ϖ C e)).isLocallyConstant,
    HasCompactSupport.intro (isCompact_box ϖ C e) fun _ hx => Set.indicator_of_notMem hx _⟩


omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
theorem box_eq_of_mem {ϖ : kˣ} {C X : Matrix A D k} {e : A → ℕ} (hX : X ∈ box ϖ C e) : box ϖ X e = box ϖ C e := by
  ext Y
  refine ⟨fun hY i j => ?_, fun hY i j => ?_⟩
  · rw [show Y i j - C i j = (Y i j - X i j) + (X i j - C i j) by ring]
    exact Valuation.map_add_le _ (hY i j) (hX i j)
  · rw [show Y i j - X i j = (Y i j - C i j) - (X i j - C i j) by ring]
    exact Valuation.map_sub_le _ (hY i j) (hX i j)


omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
theorem boxFn_eq_of_mem {ϖ : kˣ} {C X : Matrix A D k} {e : A → ℕ} (hX : X ∈ box ϖ C e) :
    boxFn ϖ X e = boxFn ϖ C e := by
  rw [boxFn, boxFn, box_eq_of_mem hX]

end GlobalTheory.RankCoinv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExactExponentsSmulMemLocalizedCoeffLattice
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.OntoExponentsLat

variable {K : Type} [Field K] [NumberField K]

theorem natCast_notMem_of_not_dvd [StarRing K] (w : HeightOneSpectrum (𝓞 K)) {m : ℕ}
    (hm : ¬ Formalism.EigenvalueLevelCeiling.plc w ∣ m) : (m : 𝓞 K) ∉ w.asIdeal := by
  intro h
  apply hm
  have h1 : ((m : ℕ) : 𝓞 K ⧸ w.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h
  unfold Formalism.EigenvalueLevelCeiling.plc
  exact (CharP.cast_eq_zero_iff (𝓞 K ⧸ w.asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal)) m).1 h1

theorem factor_mem (w : HeightOneSpectrum (𝓞 K)) (p e n : ℕ) (ν : Fin n → ℕ)
    (hpw : ∀ m : ℕ, ¬ p ∣ m → (m : 𝓞 K) ∉ w.asIdeal) (hI : Formalism.CohomologicalDescent.LA.InclZ n n le_rfl ν p e) :
    ∀ f ∈ (Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n ν).map (toK K (Fin n × Fin n)),
      ((p : K) ^ e) • f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal
        ((Formalism.GradedWeylDivisibility.weyl (𝓞 K) n n le_rfl ν).map (toK K (Fin n × Fin n))) := by
  obtain ⟨m, hm, hmx⟩ := hI
  have hm0 : (m : K) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rintro rfl
    exact hm (dvd_zero p)
  have hval : w.valuation K ((m : K)⁻¹) ≤ 1 := by
    have h1 : w.valuation K (algebraMap (𝓞 K) K (m : 𝓞 K)) = 1 :=
      (w.valuation_eq_one_iff_notMem).2 (hpw m hm)
    rw [map_natCast] at h1
    rw [map_inv₀, h1, inv_one]
  rintro _ ⟨g, hg, rfl⟩
  rw [GlobalTheory.StdDual.dualWeyl_eq, ← GlobalTheory.StdDual.image_bidSet (Int.castRingHom (𝓞 K))] at hg
  induction hg using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨b, hb, rfl⟩ := hq
    have hbD : b ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ n n ν := by
      rw [GlobalTheory.StdDual.dualWeyl_eq]
      exact Submodule.subset_span hb
    have h1 := GlobalTheory.WeylRowAll.map_mem_weyl (Int.castRingHom (𝓞 K)) le_rfl ν _ (hmx b hbD)
    have h2 := GlobalTheory.JetOpWeylLat.smul_mem_localizationAt_of_valuation w hval (Submodule.mem_map_of_mem (f := toK K (Fin n × Fin n)) h1)
    convert h2 using 1
    rw [GlobalTheory.JetOpWeylLat.toK_map_int, GlobalTheory.JetOpWeylLat.toK_map_int, map_zsmul, ← Int.cast_smul_eq_zsmul K,
      smul_smul]
    congr 1
    push_cast
    field_simp
  | zero => simpa using zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add (f := _), smul_add]
    exact add_mem ha hb
  | smul a g _ hg =>
    rw [map_smul, smul_comm]
    exact Submodule.smul_mem _ a hg

end GlobalTheory.OntoExponentsLat

namespace GlobalTheory.OntoExponentsLat

variable {K : Type} [Field K] [NumberField K]

theorem tensor_mem (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (c : K)
    (e : ι → ℕ)
    (h : ∀ τ, ∀ f ∈ (nablaSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)),
      (c ^ e τ) • f ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((delSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)))) :
    ∀ z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam),
      (c ^ ∑ τ, e τ) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  classical
  have key : ∀ y ∈ nabStd K lam, (c ^ ∑ τ, e τ) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
    intro y hy
    unfold nabStd Formalism.GradedWeylDivisibility.tensorLat at hy
    induction hy using Submodule.span_induction with
    | mem P hP =>
      obtain ⟨F, hF, rfl⟩ := hP
      choose t ht hFt using fun τ => (lc_mem_locP w _ _).1 (h τ (F τ) (hF τ))
      have hnot : (∏ τ, t τ) ∉ w.asIdeal :=
        Submonoid.prod_mem w.asIdeal.primeCompl (t := Finset.univ) (f := t) (fun τ _ => ht τ)
      refine (lc_mem_locP w _ _).2 ⟨∏ τ, t τ, hnot, ?_⟩
      have hFt' : ∀ τ, (algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ ∈
          (delSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)) := fun τ => by
        have e1 : t τ • c ^ e τ • F τ = (algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ :=
          (algebraMap_smul K (t τ) _).symm.trans (smul_smul _ _ _)
        convert hFt τ using 1
        exact e1.symm
      have hmem : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ ((algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ)) ∈ delStd K lam :=
        Submodule.subset_span ⟨_, hFt', rfl⟩
      have e2 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ ((algebraMap (𝓞 K) K (t τ) * c ^ e τ) • F τ)) =
          ((algebraMap (𝓞 K) K (∏ τ, t τ)) * c ^ ∑ τ, e τ) • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (F τ) := by
        simp only [map_smul, MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod, map_mul,
          Formalism.GradedWeylDivisibility.blockEmb, MvPolynomial.rename_C]
        congr 2
        rw [← map_prod, Finset.prod_pow_eq_pow_sum]
      rw [e2] at hmem
      convert hmem using 1
      exact (algebraMap_smul K (∏ τ, t τ) _).symm.trans (smul_smul _ _ _)
    | zero => simpa using zero_mem _
    | add a b _ _ ha hb =>
      rw [smul_add]
      exact add_mem ha hb
    | smul a y _ hy =>
      have e3 : (c ^ ∑ τ, e τ) • a • y = a • (c ^ ∑ τ, e τ) • y := smul_comm _ _ _
      convert Submodule.smul_mem _ a hy using 1
      exact e3
  intro z hz
  obtain ⟨s, hs, hsz⟩ := (lc_mem_locP w _ _).1 hz
  obtain ⟨t, ht, htz⟩ := (lc_mem_locP w _ _).1 (key _ hsz)
  refine (lc_mem_locP w _ _).2 ⟨t * s, lc_mul_notMem w ht hs, ?_⟩
  convert htz using 1
  exact (mul_smul t s _).trans (congrArg (t • ·) (smul_comm s _ z))

end GlobalTheory.OntoExponentsLat

namespace GlobalTheory.OntoExponentsLat

theorem exZ_sum_smul_mem_locP_delAtr :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ)
      (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)),
      Submodule.IsFullLattice E L → ∀ (w : HeightOneSpectrum (𝓞 K)), ∀ x ∈ nabAtr emb lam L,
        (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) • x ∈
          Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delAtr emb lam L) := by
  intro E K _ _ _ _ _ ι _ n emb lam L hL w x hx
  have hM : ∀ τ, Submodule.IsFullLattice K (dualFr (tauLat emb τ L)) := fun τ =>
    du_dualFr_lattice basisAtEx _ (tauLatLattice E K ι n emb τ L hL)
  choose B hB using fun τ => basisAtEx K n _ (hM τ) w
  have hx1 : (x : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ L)) :=
    lc_le_locP w _ hx
  rw [(nabDelLoc K ι n lam _ hM w B hB).1] at hx1
  obtain ⟨z, hz, hzx⟩ := hx1
  have hfac : ∀ τ, ∀ f ∈ (nablaSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n)),
      ((Formalism.EigenvalueLevelCeiling.plc w : K) ^ Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w)) • f ∈
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((delSq (𝓞 K) n (lam τ)).map (toK K (Fin n × Fin n))) := fun τ =>
    factor_mem w (Formalism.EigenvalueLevelCeiling.plc w) _ n (lam τ).natW (fun m hm => natCast_notMem_of_not_dvd w hm)
      (Formalism.CohomologicalDescent.LA.exact_z_specialization n n le_rfl _ (natW_antitone _) _ (Formalism.EigenvalueLevelCeiling.plc_prime w))
  have hz' := tensor_mem w lam (Formalism.EigenvalueLevelCeiling.plc w : K) _ hfac z hz
  refine (GlobalTheory.LvT.Built.ValLat.mem_localization_delAtr emb lam w hL B hB _).2 ⟨_, hz', ?_⟩
  have e1 : (actP lam B) z = (x : Pol K ι n) := hzx
  rw [map_smul, e1]
  refine (algebraMap_smul K (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^
    (∑ τ, Formalism.CohomologicalDescent.LA.exZ n n le_rfl (lam τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) (x : Pol K ι n)).symm.trans ?_
  simp only [map_pow, map_natCast]

end GlobalTheory.OntoExponentsLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open GlobalTheory.LieVB GlobalTheory.Conormal

namespace GlobalTheory.SqZeroPt

theorem zeroSec_sqZeroMap (O : Type) [CommRing O] (M N : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N]
    [IsCentralScalar O N] (l : M →ₗ[O] N) :
    zeroSec O N ≫ GlobalTheory.GrpTangent.sqZeroMap l = zeroSec O M := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  simp

theorem Phi_sqZeroMap_comp : ∀ (O : Type) [CommRing O] (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (A : Over (Sp O)) [GrpObj A] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w) := by
  intro O _ M N _ _ _ _ _ _ _ _ A _ l z h h' w
  have hl := zeroSec_sqZeroMap O M N l
  rw [Phi_apply, Phi_apply, ← cotMap_comp h hl rfl h']
  obtain ⟨b, hb⟩ := (isChart O M).d_surjective (sec_hom (zeroSec O M)) ((cotMap z h).app ⊤ w)
  have e : (ConcreteCategory.hom (Scheme.Modules.Hom.app (cotMap z h ≫ cotMap (GlobalTheory.GrpTangent.sqZeroMap l) hl) ⊤)) w = (ConcreteCategory.hom (Scheme.Modules.Hom.app (cotMap (GlobalTheory.GrpTangent.sqZeroMap l) hl) ⊤)) ((ConcreteCategory.hom (Scheme.Modules.Hom.app (cotMap z h) ⊤)) w) := rfl
  rw [e, ← hb, cotMap_d (GlobalTheory.GrpTangent.sqZeroMap l) hl _ (le_preimage_top _ ⊤) (le_preimage_top _ ⊤), kappa_d, kappa_d, appLE_top]
  change (toTsze O N ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)).appTop b)).snd = _
  rw [show toTsze O N ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)).appTop b) = TrivSqZeroExt.map l (toTsze O M b) from
    congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)) b)]
  simp

end GlobalTheory.SqZeroPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTranslateThetaCoordinateOfRealPartLaw
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem U_thY_of_law : ∀ {D : D7} (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B'.1 * T.gram * B'.1 = 1 → ∀ (δ : ℂ), δ ≠ 0 → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (f : WO S T → ℂ) (c : ℂ), (∀ z : GlobalTheory.FockCompare.RW T S, f (GlobalTheory.FockCompare.iotaW σ T S (z + GlobalTheory.VacUnique.infRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1))) = c * Complex.exp (-(↑Real.pi * Complex.I) * ↑(-(GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)) z))) * f (GlobalTheory.FockCompare.iotaW σ T S z)) → ∀ Y, Formalism.MainNotions.TaylorLogMetric.U D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M) (GlobalTheory.VacRealForm.thY σ S T (fun τ => B.1.map (tauE D τ)) (fun τ => B'.1.map (tauE D τ)) f δ) Y = c * GlobalTheory.VacRealForm.thY σ S T (fun τ => B.1.map (tauE D τ)) (fun τ => B'.1.map (tauE D τ)) f δ Y := by
  intro D σ S T B B' hB hB' δ hδ M f c hf Y
  set Bc : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ := fun τ => B.1.map (tauE D τ) with hBc
  set B'c : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ := fun τ => B'.1.map (tauE D τ) with hB'c
  set X : RW T S := Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M with hXdef
  set Z : RW T S := δ⁻¹ • Y with hZ
  have hY : Y = δ • Z := by rw [hZ, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  have hinv : ∀ τ, ((B⁻¹ : GL (Fin S.rank) D.host.E).1).map (tauE D τ) = (B.1.map (tauE D τ))⁻¹ := fun τ =>
    (Matrix.inv_eq_left_inv (by
      rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)])).symm
  have hX : infRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) = frPt Bc B'c X := by
    funext τ
    show (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1).map (tauE D τ) = B'c τ * Matrix.of (X τ) * (Bc τ)⁻¹
    rw [Matrix.map_mul, Matrix.map_mul, hinv]
    rfl
  have hadd : δ⁻¹ • (Y + δ • X) = Z + X := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  have hfr : frPt Bc B'c (Z + X) = frPt Bc B'c Z + frPt Bc B'c X := (frL Bc B'c).map_add Z X
  have hlaw := hf (frPt Bc B'c Z)
  rw [hX] at hlaw
  have hom : omO S T (frPt Bc B'c X) (frPt Bc B'c Z) =
      ∑ τ, ∑ a, ∑ b, 2 * (((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * Complex.I * (starRingEnd ℂ (Z τ a b) * X τ a b)).re :=
    omO_frame B B' hB hB' X Z
  have harea : Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) =
      Complex.normSq δ * (Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d / 2 :=
    GlobalTheory.MomDict.area_lamOf D _ δ D.host.ccK_ne_bot
  have hxi := (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D).1
  have hN : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by
    have h : Ideal.absNorm D.host.ccK ≠ 0 := fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast h
  have hd : Real.sqrt D.host.d ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)).ne'
  have hδn : Complex.normSq δ ≠ 0 := (Complex.normSq_pos.2 hδ).ne'
  have hHf : ∀ u v : RW T S, Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • u) (δ • v) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, u τ a b * starRingEnd ℂ (v τ a b) := by
    intro u v
    show (∑ τ, ∑ a, ∑ b, (δ • u) τ a b * starRingEnd ℂ ((δ • v) τ a b)) /
      (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) : ℂ) = _
    have e : ∀ τ a b, (δ • u) τ a b * starRingEnd ℂ ((δ • v) τ a b) =
        (Complex.normSq δ : ℂ) * (u τ a b * starRingEnd ℂ (v τ a b)) := fun τ a b => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← Complex.mul_conj]; ring
    simp only [e, ← Finset.mul_sum]
    rw [harea, hxi]
    have h1 : ((Complex.normSq δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hδn
    have h2 : ((Ideal.absNorm D.host.ccK : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN
    have h3 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
    generalize (∑ τ, ∑ a, ∑ b, u τ a b * starRingEnd ℂ (v τ a b)) = s
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    field_simp
  have key : -(↑Real.pi * Complex.I) * ↑(-(omO S T (frPt Bc B'c X) (frPt Bc B'c Z))) +
      ((Real.pi * Formalism.L2.Pj.xiR D * sqSum (Z + X) : ℝ) : ℂ) +
      (-(Real.pi : ℂ) * Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Z) (δ • X) -
        (Real.pi : ℂ) * Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X) (δ • X) / 2) =
      ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ) := by
    have hOm : omO S T (frPt Bc B'c X) (frPt Bc B'c Z) =
        2 * Formalism.L2.Pj.xiR D * (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)).im := by
      rw [hom]
      simp only [Complex.im_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im]
      ring
    have hSq : sqSum (Z + X) = sqSum Z + 2 * (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)).re + sqSum X := by
      unfold sqSum
      simp only [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Pi.add_apply, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.conj_re, Complex.conj_im]
      ring
    have hQ : (∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) = ((sqSum X : ℝ) : ℂ) := by
      unfold sqSum
      push_cast
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hHf, hHf, hOm, hSq, hQ]
    generalize (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) = p
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] <;> ring
  show gZ σ S T Bc B'c f (δ⁻¹ • (Y + δ • X)) * _ = c * gZ σ S T Bc B'c f (δ⁻¹ • Y)
  rw [hadd, ← hZ]
  unfold gZ
  rw [hfr, hlaw, hY, ← key, Complex.exp_add, Complex.exp_add]
  ring

end GlobalTheory.VacRealForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
section
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacLn

def trPair (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun x x' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)])
    (fun c x y => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul])
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
    (fun c x y => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul])

theorem trPair_apply {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x y : κ → mixedEmbedding.mixedSpace F) :
    trPair F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

def coord {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} (d : Darboux B κ) (w : W) :
    (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) :=
  (fun i => evI F ((d.e w).1 i), fun i => evI F ((d.e w).2 i))

end GlobalTheory.VacLn
end
end

