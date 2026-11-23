module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeylConjugateOfUnitarySatakeDiagDoubleCosets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0511
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetSplitPlaceLatticeIntersection
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
section
noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun.Orbit
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (WeylConjU bcParam bcParam_of_weylConj)

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n q : ℕ} {ϖ ϖ' : L}

theorem exists_dosetInd_eq (hU : IsUnramInv ϖ σ q) (hU' : IsUnramInv ϖ' σ q) {d : Fin n → ℤ} {t : GU σ n}
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) :
    ∃ t' : GU σ n, t'.1.1 = Matrix.diagonal (fun i => ϖ' ^ d i) ∧ dosetInd ℂ (KU σ n) t' = dosetInd ℂ (KU σ n) t := by
  have h0 := GlobalTheory.InertThetaCompare.unif_ne_zero hU
  have h0' := GlobalTheory.InertThetaCompare.unif_ne_zero hU'
  have hv : ∀ a : ℤ, Valued.v (ϖ ^ a) = WithZero.exp (-a) := fun a => by
    simpa using GlobalTheory.InertThetaCompare.val_prod_zpow (ϖ := ϖ) hU.2.2.2.1 (Finset.univ : Finset Unit) fun _ => a
  have hd : ∀ i, d i + d i.rev = 0 := fun i => by
    have h1 := P.fSatake_unit_diag (P.fSatake_borel_of_diag ht) i
    rw [ht, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, map_zpow₀, hU.2.2.1, ← zpow_add₀ h0] at h1
    have h2 := hv (d i + d i.rev)
    rw [h1, map_one, eq_comm, WithZero.exp_eq_one] at h2
    omega
  obtain ⟨k, hk, hk'⟩ := P.fSatake_diag_exists (σ := σ) (fun i : Fin n => (ϖ' / ϖ) ^ d i) fun i => by
    rw [map_zpow₀, map_div₀, hU.2.2.1, hU'.2.2.1, ← zpow_add₀ (div_ne_zero h0' h0), hd, zpow_zero]
  have hK : k ∈ KU σ n := P.fSatake_diag_mem_K hk hk' fun i => by
    rw [map_zpow₀, map_div₀, hU.2.2.2.1, hU'.2.2.2.1, div_self WithZero.coe_ne_zero, one_zpow]
  refine ⟨t * k, ?_, ?_⟩
  · rw [Subgroup.coe_mul, Units.val_mul, ht, hk, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← mul_zpow, mul_div_cancel₀ _ h0]
  · rw [dosetInd, dosetInd, DoubleCoset.doubleCoset_eq_of_mem
      (DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, k, hK, by rw [one_mul]⟩)]

variable [CompleteSpace L] {V : Type} [AddCommGroup V] [Module ℂ V] {α β : Fin (n / 2) → ℂˣ}

theorem satU_of_weylConj (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) (e : WeylConjU α β) :
    SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h (fun i => (β i : ℂ)) :=
  unitarySatakeTransform_weylConjugate_invariant _root_.GlobalTheory.SatakeWeyl.satWeyl hU hh e

theorem weylConj_of_dosetInd (hU : IsUnramInv ϖ σ q)
    (h : ∀ (d : Fin n → ℤ) (t : GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      SatU ϖ q (dosetInd ℂ (KU σ n) t) (fun i => (α i : ℂ)) = SatU ϖ q (dosetInd ℂ (KU σ n) t) fun i => (β i : ℂ)) :
    WeylConjU α β := weylConjugate_of_unitarySatake_diagDoubleCosets _root_.GlobalTheory.SatakeWeyl.satWeyl hU h

theorem satU_eq_iff_weylConj (hU : IsUnramInv ϖ σ q) :
    (∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h fun i => (β i : ℂ)) ↔ WeylConjU α β :=
  ⟨fun h => weylConj_of_dosetInd hU fun _ _ _ _ => h _ (Final.DosetIndMem _ _ _ _),
    fun e _ hh => satU_of_weylConj hU hh e⟩

theorem bcParam_eq_of_satU_eq (hU : IsUnramInv ϖ σ q)
    (h : ∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h fun i => (β i : ℂ)) :
    bcParam n α = bcParam n β := bcParam_of_weylConj ((satU_eq_iff_weylConj hU).1 h)

variable {ρ : Representation ℂ (GU σ n) V} {x : V}

theorem IsSatVecU.unique (hU : IsUnramInv ϖ σ q) (h : IsSatVecU ϖ q ρ x α) (h' : IsSatVecU ϖ q ρ x β) :
    WeylConjU α β :=
  (satU_eq_iff_weylConj hU).1 fun t ht => smul_left_injective ℂ h.1 ((h.2.2 t ht).symm.trans (h'.2.2 t ht))

end Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Place

variable {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}

theorem toCompl_surjective (h : w.under (𝓞 F) = v) : Function.Surjective (toCompl h) := fun y => by
  obtain ⟨a, ha⟩ := (finAdEquiv F E).surjective (Neutral.B1.finiteSingle E w y)
  refine ⟨_, (finAdEquiv_apply h a).symm.trans ?_⟩
  rw [ha]
  classical exact Pi.mulSingle_eq_same (M := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) w y

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {V : Type} [AddCommGroup V] [Module ℂ V] {h : w.under (𝓞 F) = v}

theorem IsConjAt.unique {c c' : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c)
    (hc' : IsConjAt σ h c') : c = c' := RingHom.ext fun y => by
  obtain ⟨z, rfl⟩ := toCompl_surjective h y
  rw [hc, hc']

variable {ρ : Representation ℂ (GLoc σ J v) V} {x : V} {B B' : Multiset ℂˣ}

theorem IsParamVec.unique (hx : IsParamVec σ J L h ρ x B) (hx' : IsParamVec σ J L h ρ x B') : B = B' := by
  by_cases hv : IsSplit (E := E) v
  · exact hx.unique_of_isSplit hv hx'
  obtain ⟨-, c, ϖ, e, α, hU, he, hα, rfl⟩ := hx.resolve_left fun h => hv h.1
  obtain ⟨-, c', ϖ', e', β, hU', he', hβ, rfl⟩ := hx'.resolve_left fun h => hv h.1
  obtain rfl := he.1.unique he'.1
  exact bcParam_of_weylConj (((hα.of_chart he he').of_unif hU hU').unique hU' hβ)

theorem HasParam.unique (hρ : HasParam σ J L h ρ B) (hρ' : HasParam σ J L h ρ B') : B = B' := by
  obtain ⟨x, hx⟩ := hρ.exists_vec
  exact hx.unique (hρ'.isParamVec hx.mem_fixed hx.ne_zero)

theorem IsSysParam.unique {c : List ℤ → ℂ} (hc : IsSysParam σ n h c B) (hc' : IsSysParam σ n h c B') : B = B' := by
  rcases hc with ⟨hv, hB, hc⟩ | ⟨hw, τ, ϖ, α, hU, hτ, rfl, hc⟩ <;>
    rcases hc' with ⟨hv', hB', hc'⟩ | ⟨hw', τ', ϖ', β, hU', hτ', rfl, hc'⟩
  · exact eq_of_satEig_eq (qV_ne_zero w) hB hB' fun j hj => (hc j hj).symm.trans (hc' j hj)
  · exact absurd hv (not_isSplit_of_isInertAt hw')
  · exact absurd hv' (not_isSplit_of_isInertAt hw)
  · obtain rfl := hτ.unique hτ'
    refine bcParam_of_weylConj (weylConj_of_dosetInd hU fun d t hd ht => ?_)
    obtain ⟨t', ht', e⟩ := exists_dosetInd_eq hU hU' ht
    rw [← hc d t hd ht, hc' d t' hd ht', e, satU_indep hU hU' (Final.DosetIndMem _ _ _ _)]

end Place

section Global

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {S : Set (HeightOneSpectrum (𝓞 F))} {V : Type} [AddCommGroup V] [Module ℂ V]
  {Vl : HeightOneSpectrum (𝓞 F) → Type} [∀ v, AddCommGroup (Vl v)] [∀ v, Module ℂ (Vl v)]
  {π : ∀ v, Representation ℂ (GLoc σ J v) (Vl v)} {c c' : Fam E} {w : HeightOneSpectrum (𝓞 E)}

theorem IsParamVecOff.unique {ρ : Representation ℂ (GAd σ J) V} {x : V} (h : IsParamVecOff σ J L S ρ x c)
    (h' : IsParamVecOff σ J L S ρ x c') (hw : w ∉ above E S) : c w = c' w :=
  (h _ hw w rfl).unique (h' _ hw w rfl)

theorem IsSysParamOff.unique {s : HeightOneSpectrum (𝓞 E) → List ℤ → ℂ} (h : IsSysParamOff σ n S s c)
    (h' : IsSysParamOff σ n S s c') (hw : w ∉ above E S) : c w = c' w :=
  (h _ hw w rfl).unique (h' _ hw w rfl)

theorem LSTw_congr (h : ∀ w ∉ above E S, c w = c' w) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (s : ℂ) :
    LSTw S c m s = LSTw S c' m s := eulerProd_congr (fun w hw => by rw [twist, twist, h w hw]) s

end Global

end GlobalTheory.LFun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactAdelesRationalPointsFiniteEventuallyZeroStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Ω : Set (AF F ⊗[F] E)), IsCompact Ω → {x : E | inclR (F := F) (AF F) x ∈ Ω}.Finite ∧ ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, inclR (F := F) (AF F) x = (halfE F E).1 ^ m * ω → x = 0 := by
  first | exact @GlobalTheory.Eis.Conv.Discr.finite_and_eventually_eq_zero | exact GlobalTheory.Eis.Conv.Discr.finite_and_eventually_eq_zero | (intros; apply GlobalTheory.Eis.Conv.Discr.finite_and_eventually_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetSplitPlaceLatticeIntersectionStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingNorm_det_splitPlace_lattice_intersection : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), IsSelfDualAt σ J L v → ∀ (τ : E →ₐ[F] Fv F v) (β : GL (Fin n) (Fv F v)), IsSplitBasis τ L β → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∀ d : Fin n → (Fv F v)ˣ, IsElemDiv (splitEquivIn h hJ τ β g) d → absEv F E v (Matrix.GeneralLinearGroup.det α) = ∏ i, min ‖(d i : Fv F v)‖₊ ‖(d i : Fv F v)‖₊⁻¹ := by
  first | exact @GlobalTheory.SplitInterDet.absEv_det_split | exact GlobalTheory.SplitInterDet.absEv_det_split | (intros; apply GlobalTheory.SplitInterDet.absEv_det_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmAdeleSplitComplexFiniteAdelesStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmAdele_split_complex_finiteAdeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ e : (AF F ⊗[F] E) ≃+* (InfinitePlace E → ℂ) × FiniteAdeleRing (𝓞 E) E, Continuous e.symm ∧ (∀ x : E, e (inclR (F := F) (AF F) x) = (fun w : InfinitePlace E => w.embedding x, algebraMap E (FiniteAdeleRing (𝓞 E) E) x)) ∧ e (halfE F E).1 = (fun _ => 2⁻¹, 1) := by
  first | exact @GlobalTheory.Eis.Conv.AdeleCMSplit.exists_adele_split | exact GlobalTheory.Eis.Conv.AdeleCMSplit.exists_adele_split | (intros; apply GlobalTheory.Eis.Conv.AdeleCMSplit.exists_adele_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtLinearIndependent
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues (IsCoefExt RationalValues RationalValuesAt ValuesIn)
open GlobalTheory.Proof.PlaceExtensionValues

namespace GlobalTheory.RationalValuesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coef

variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} {ι : K →+* K'}
  {I : Type} [Fintype I] {n : ℕ} {lam : I → DomWeight n} {W : Type} [AddCommGroup W] [Module ℂ W]
  {c₀ : VV K lam →ₛₗ[σ] W} {c' c'' : VV K' lam →ₛₗ[σ'] W}

theorem exists_basis_val (lam : I → DomWeight n) (ι : K →+* K') (j : VVIdx lam) :
    ∃ v : VV K lam, ((bVV K' lam j : VV K' lam) : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) := by
  obtain ⟨F, hF, hj⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc ι lam j
  exact ⟨⟨F, hF⟩, (bVV_coe _ _ _).trans hj⟩

theorem ext_unique (h : IsCoefExt ι lam c₀ c') (h' : IsCoefExt ι lam c₀ c'') : c' = c'' := by
  refine (bVV K' lam).ext fun j => ?_
  obtain ⟨v, hv⟩ := exists_basis_val lam ι j
  rw [h v _ hv, h' v _ hv]

end Coef

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem existsUnique_c0BC (i : Fin D.R.m) {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ)
    (hσ : σ'.comp jL = D.what₂.embLL) (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) :
    ∃! c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, CoefficientBaseChange R i jL σ' c₀ c' := by
  obtain ⟨c', hc⟩ := GlobalTheory.Mem.PlaceVal.exists_ext_VV (W := (R.cV i).W) jL σ' hσ (FWT.lamV D i) c₀
  exact ⟨c', hc, fun c'' hc'' => ext_unique ((isCoefExt_iff_c0BC R i jL c₀ c'').2 hc'') ((isCoefExt_iff_c0BC R i jL c₀ c').2 hc)⟩

end Row

end GlobalTheory.RationalValuesObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SkewHermitianAdelicCoverOfAdeleCoverStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitian_adelic_cover_of_adele_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (b C₀ : ℝ) (Ω₀ : Set (AF F)), IsCompact Ω₀ → (∀ m : ℕ, ∃ Y : Finset (AF F), (Y.card : ℝ) ≤ C₀ * b ^ m ∧ ∀ a : AF F, ∃ x : F, ∃ y ∈ Y, ∃ ω ∈ Ω₀, a = algebraMap F (AF F) x + y + (halfInf F).1 ^ m * ω) → ∀ n : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (C : ℝ), IsCompact Ω ∧ ∀ m : Fin n → ℕ, ∃ Y : Finset (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ C * ∏ i, (b ^ 2) ^ (n * m i) ∧ ∀ S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) S = -S → ∃ S₀ : Matrix (Fin n) (Fin n) E, ∃ y ∈ Y, ∃ ω : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (∀ i j, ω i j ∈ Ω) ∧ S = S₀.map (inclR (F := F) (AF F)) + y + Matrix.diagonal (fun i => (halfE F E).1 ^ m i) * ω * Matrix.diagonal (fun i => (halfE F E).1 ^ m i) := by
  first | exact @GlobalTheory.Eis.Conv.CovSkew.cover_skew | exact GlobalTheory.Eis.Conv.CovSkew.cover_skew | (intros; apply GlobalTheory.Eis.Conv.CovSkew.cover_skew <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorIdeleNormalizedAbsIdeleHalfAtInfinityStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorIdeleNormalizedAbs_ideleHalfAtInfinity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → absE F E (halfE F E) = ((4 : ℝ≥0) ^ Fintype.card (InfinitePlace F))⁻¹ := by
  first | exact @GlobalTheory.Eis.Conv.absE_halfE | exact GlobalTheory.Eis.Conv.absE_halfE | (intros; apply GlobalTheory.Eis.Conv.absE_halfE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCosetStatement
section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDoubleCoset_of_GLintDoubleCoset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (g g' : GU σ n) (a b : GL (Fin n) L), a ∈ GLint (Fin n) (intL L) → b ∈ GLint (Fin n) (intL L) → (g' : GL (Fin n) L) = a * g * b → ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g' = k₁ * g * k₂ := by
  first | exact @GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL | exact GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL | (intros; apply GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL <;> assumption)
end

