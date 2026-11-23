module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0490
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0562
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientDualCrystallineAndPureOfDecomp
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.MainNotions.TruncatedSeriesCountingIdentities (Decl CoefExt locC chi1C)

namespace GlobalTheory.AmbWT

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : CoefExt D i w hw)

def coef : D.nd.O i →+* ↥C.LL.1 := C.inc.comp (D.nbr i w hw).toLL

def grp (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Br.G D.nbr i w hw →* GE D.nd :=
  (decS D.nd w).comp (Br.iota D.nbr i w hw)

theorem locC_apply {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    locC C M g = (M (grp hw g)).map (coef C) := rfl

theorem localizedCoefficientChar_apply (g : Br.G D.nbr i w hw) :
    chi1C C g = Units.map (coef C : D.nd.O i →* ↥C.LL.1) (chiU D.nd i 1 (grp hw g)) := rfl

theorem locC_rTwO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    locC C (rTwO D.nd i r x) = twistM (locC C (rO D.nd i r x)) (chi1C C)⁻¹ := by
  refine MonoidHom.ext fun g => Matrix.ext fun a b => ?_
  rw [locC_apply]
  show coef C ((((chiU D.nd i 1)⁻¹ (grp hw g) : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (grp hw g) a b) =
    ((((chi1C C)⁻¹ g) : (↥C.LL.1)ˣ) : ↥C.LL.1) * (locC C (rO D.nd i r x) g) a b
  rw [map_mul, locC_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, localizedCoefficientChar_apply]
  rfl


open Classical in
theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambW (D := D) i ρ π dc ∧ EmbeddingTypes.ambT2 (D := D) i ρ π dc := by
  intro D i r ρ π dc hG hd
  have hd' : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
    obtain ⟨e, he⟩ := hd
    refine ⟨e, fun g u => ?_⟩
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.overK, GlobalTheory.SummandJumps.matRep_apply]
    exact he g u
  have hc : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : CoefExt D i w hw),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locC C (WpO D.nd i ρ π))) ∧
        IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locC C (T2O D.nd i ρ π))) := by
    intro w hw C
    have h1 := (hG w hw C).2 π
    rw [← locC_rTwO] at h1
    exact (GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hd').1 h1
  refine ⟨fun _ w hw _ C => (hc w hw C).1, fun _ w hw _ C => ⟨(hc w hw C).2, ?_, ?_⟩⟩
  · exact (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) (D.nbr i w hw).Kw C.LL _ _ (hc w hw C).2).1
  · exact (hG w hw C).1.2.2.2.2.2.2

end GlobalTheory.AmbWT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisImagesBasisBdRplus
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BKGal.JumpDR.BasisGlue.exists_basis {R W : Type} [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W))
    (hmul : ∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) (hone : ∀ w : W, act 1 w = w) (eD : R)
    (hbij : Function.Bijective (act eD)) (F : ℤ → W → Prop) (hshift : ∀ (y : W) (j : ℤ), F j y ↔ F (j + 1) (act eD y))
    {ι : Type} [Fintype ι] [DecidableEq ι] (β β₀ : ℕ) (g h b : ι → W) (hg : ∀ i, act (eD ^ β₀) (g i) = h i)
    (hspan : ∀ w, F ((β₀ + β : ℕ) : ℤ) w ↔ ∃ d : ι → R, w = ∑ i, act (d i) (h i))
    (hb0 : ∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ k, act (d k) (b k))
    (hbi : ∀ d : ι → R, ∑ k, act (d k) (b k) = 0 → ∀ k, d k = 0) :
    ∃ f : ι → W, (∀ i, act (eD ^ β) (f i) = g i) ∧ (∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ i, act (d i) (f i)) ∧
      ∀ d : ι → R, ∑ i, act (d i) (f i) = 0 → ∀ i, d i = 0 := by
  have hcomm : ∀ (d d' : R) (w : W), act d (act d' w) = act d' (act d w) := by
    intro d d' w
    rw [← hmul, ← hmul, mul_comm]
  have hpow : ∀ (n : ℕ) (w : W), act (eD ^ n) w = (act eD)^[n] w := by
    intro n
    induction n with
    | zero => intro w; rw [pow_zero, hone]; rfl
    | succ n ih => intro w; rw [pow_succ', hmul, ih, Function.iterate_succ_apply']
  have hinj : ∀ n : ℕ, Function.Injective (act (eD ^ n)) := by
    intro n x x' hxx
    rw [hpow, hpow] at hxx
    exact (hbij.1.iterate n) hxx
  have hsh : ∀ (n : ℕ) (w : W) (j : ℤ), F j w ↔ F (j + n) (act (eD ^ n) w) := by
    intro n
    induction n with
    | zero => intro w j; rw [pow_zero, hone, Nat.cast_zero, add_zero]
    | succ n ih =>
      intro w j
      rw [ih w j, hshift (act (eD ^ n) w) (j + n), pow_succ', hmul, Nat.cast_succ, ← add_assoc]
  have hsingle : ∀ (v : ι → W) (i : ι), ∑ k, act ((Pi.single i (1 : R) : ι → R) k) (v k) = v i := by
    intro v i
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, map_zero, AddMonoidHom.zero_apply])
      (fun h => (h (Finset.mem_univ i)).elim), Pi.single_eq_same, hone]
  let ginv : W → W := (Equiv.ofBijective _ hbij).symm
  have hginv : ∀ x, act eD (ginv x) = x := fun x => (Equiv.ofBijective _ hbij).apply_symm_apply x
  have h1 : ∀ i, act (eD ^ β) (ginv^[β] (g i)) = g i := by
    intro i
    rw [hpow]
    exact Function.RightInverse.iterate hginv β _
  have h2 : ∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ i, act (d i) (ginv^[β] (g i)) := by
    have hf : ∀ i, act (eD ^ (β₀ + β)) (ginv^[β] (g i)) = h i := by
      intro i
      rw [pow_add, hmul, hpow β, Function.RightInverse.iterate hginv β, hg]
    intro v
    rw [hsh (β₀ + β) v 0, zero_add, hspan]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, hinj (β₀ + β) ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hd, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcomm, hf i]
    · rintro ⟨d, rfl⟩
      refine ⟨d, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcomm, hf i]
  refine ⟨fun i => ginv^[β] (g i), h1, h2, ?_⟩
  refine _root_.GlobalTheory.linIndep_of_mutual_span_of_indep R W act hmul hone ι b _ hbi ?_ ?_
  · intro i
    exact (hb0 _).1 ((h2 _).2 ⟨Pi.single i 1, (hsingle (fun i => ginv^[β] (g i)) i).symm⟩)
  · intro k
    exact (h2 _).1 ((hb0 _).2 ⟨Pi.single k 1, (hsingle b k).symm⟩)


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.BKGal.JumpDR.basis_images : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∃ f : ι → T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ i, A ((ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) ^ β) (f i) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1)))) ∧ (∀ v, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) ↔ ∃ d : ι → OD l ↥(OL LL), v = ∑ i, A (d i) (f i)) ∧ ∀ d : ι → OD l ↥(OL LL), ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0 := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI Td hC X hX act hA β y hy
  obtain ⟨hmul, hone⟩ := _root_.GlobalTheory.BKGal.JumpDR.odAct_mul_one l LL T Pl AI Td act hA
  obtain ⟨hbij, hshift⟩ := GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV l a e ϖ LL T Pl AI Td act hA
  obtain ⟨α, β0, hα, hβ0⟩ := P.exists_exponents
  have hLM1 : ∀ v ∈ P.M, E ↥LL.1 l e ^ (β0 + β) • v ∈ P.L := by
    intro v hv
    have := P.L.smul_mem (⟨_, pow_mem (E_mem l e _) β⟩ : A ↥(OL LL) ↥LL.1) (hβ0 v hv)
    rw [pow_add, mul_comm, mul_smul]
    exact this
  have hβ1 : ∀ τ j i, E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1 := by
    intro τ j i
    have hv : (fun (_ : ZMod a) (i' : ι) => if i' = i then (1 : (↥LL.1)⟦X⟧) else 0) ∈ P.M := by
      refine mem_tot.2 fun τ' i' => ?_
      show (if i' = i then (1 : (↥LL.1)⟦X⟧) else 0) ∈ A ↥(OL LL) ↥LL.1
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h2 := (P.mem_extc_iff.1 (mem_tot.1 (hLM1 _ hv) τ)) j
    convert h2 using 1
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have hy1 : ∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e)
      (Ehat ↥(OL LL) ↥LL.1 l e ^ β0 * y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e)
      (Ehat ↥(OL LL) ↥LL.1 l e) ^ (β0 + β) * hat ↥(OL LL) l e (P.mxInv τ j i) := fun τ j i =>
    (map_mul _ _ _).trans ((congrArg₂ (· * ·) (map_pow _ _ _) (hy τ j i)).trans
      ((mul_assoc _ _ _).symm.trans (congrArg (· * _) (pow_add _ _ _).symm)))
  have hyA := _root_.GlobalTheory.BK.coordE_mxInv_eq_ofA l a e ϖ LL ι P (β0 + β) (fun τ j i => Ehat ↥(OL LL) ↥LL.1 l e ^ β0 * y τ j i) hy1 hβ1
  have hg : ∀ i, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β0)
      (∑ j, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1)))) =
      ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1
        (fun τ => ⟨E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i, hβ1 τ j i⟩))) (X (jB (Pi.single j 1))) := by
    intro i
    refine (map_sum (act (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β0)) _ _).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    refine (hmul _ _ _).symm.trans (congrArg (fun z => act z (X (jB (Pi.single j 1)))) ?_)
    refine Eq.trans ?_ (PiSys.iD_ofA (thetaW a LL) ↥LL.1 ϖ _)
    have hpt : (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β0 * (fun τ => y τ j i) =
        fun τ => ofA ↥(OL LL) ↥LL.1 l e ⟨E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i, hβ1 τ j i⟩ :=
      funext fun τ => hyA τ j i
    exact (congrArg (· * ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i))
      (map_pow (ϖ.iD (thetaW a LL) ↥LL.1) (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) β0).symm).trans
      ((map_mul (ϖ.iD (thetaW a LL) ↥LL.1) _ _).symm.trans (congrArg (ϖ.iD (thetaW a LL) ↥LL.1) hpt))
  have hspan := GlobalTheory.T.breuilKisin_filtration_span_deRhamLattice hF l a e ϖ LL hl2 ι P T I jB Pl AI Td hC X hX act hA α (β0 + β) hα hLM1 hβ1
  obtain ⟨b⟩ := _root_.GlobalTheory.BKGal.IdentRank.main l a e ϖ LL ι P T I
  obtain ⟨hb0, hbi⟩ := GlobalTheory.T.coeffDeRhamPlus_basis_tensorLattice_free l LL T Pl AI Td act hA ι b
  exact GlobalTheory.BKGal.JumpDR.BasisGlue.exists_basis act hmul hone _ hbij
    (fun (j : ℤ) (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) => v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j)) hshift β β0
    (fun i => ∑ j, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1))))
    (fun i => ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1
        (fun τ => ⟨E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i, hβ1 τ j i⟩))) (X (jB (Pi.single j 1))))
    (fun k => ((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) hg hspan hb0 hbi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinCoproductUnitCocycleIdentities
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem height_rel_unit_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A),
    ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) →
    ∀ (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f₀) bk.J ι →
    (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧
    ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl →
      k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  intro l _ K bk d ρ τ s ht En ε hε B f₀ ι tb
  have H := GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk B.A (BK.hf f₀) ι tb
  have hinj := H.1
  have hE := H.2.1
  have key : ∀ k : Hom En.Q B, ht.Rel (BK.hf f₀ X) (k.comp En.inl) (k.comp En.inr)
      ((ε.map k.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := by
    intro k
    have H2 := GlobalTheory.T.discPeriod_comparison_relation_map_prismHom l K bk d ρ τ s ht En.Q B En.inl En.inl En.inr f₀ k (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) hε
    refine H2.1.elim fun Fk hFk => ?_
    have h := H2.2
    have e : (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk =
        (ε.map k.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀) := Matrix.ext fun i j => hFk.ext (ε i j)
    exact e ▸ h Fk hFk
  have inj : ∀ M N : Matrix (Fin d) (Fin d) B.A, M.map (toDisc l (BK.hf f₀ X) bk.ρ₀) =
      N.map (toDisc l (BK.hf f₀ X) bk.ρ₀) → M = N := fun M N h =>
    Matrix.ext fun i j => hinj (congrFun (congrFun h i) j)
  have tr : ∀ (f f' g g' : Hom bk.prism B) (M : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)),
      f = f' → g = g' → ht.Rel (BK.hf f₀ X) f g M → ht.Rel (BK.hf f₀ X) f' g' M := fun _ _ _ _ _ hf hg h =>
    hf ▸ hg ▸ h
  refine ⟨fun k hk => ?_, fun k₁ k₂ k₃ h₁ h₂ h₃ => ?_⟩
  · have h : ht.Rel (BK.hf f₀ X) (k.comp En.inr) (k.comp En.inr)
        ((ε.map k.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := tr _ _ _ _ _ hk rfl (key k)
    have e := _root_.GlobalTheory.BSP.Height.rel_mul l K bk d ρ τ s ht B f₀ hE _ _ _ 1 1 _ (ht.rel_one _ _) (ht.rel_one _ _) h
    exact inj _ _ ((e.symm.trans (mul_one 1)).trans (Matrix.map_one _ (map_zero _) (map_one _)).symm)
  · have e1 : ht.Rel (BK.hf f₀ X) (k₁.comp En.inl) (k₂.comp En.inl)
        ((ε.map k₁.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := tr _ _ _ _ _ rfl h₁ (key k₁)
    have e3 : ht.Rel (BK.hf f₀ X) (k₁.comp En.inl) (k₂.comp En.inr)
        ((ε.map k₃.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := tr _ _ _ _ _ h₂.symm h₃.symm (key k₃)
    have e := _root_.GlobalTheory.BSP.Height.rel_mul l K bk d ρ τ s ht B f₀ hE _ _ _ _ _ _ e1 (key k₂) e3
    exact inj _ _ (Matrix.map_mul.trans e)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmpIsoOfExpansions
section
noncomputable section

namespace GlobalTheory.NL.CmpCris

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Series

variable {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M]

theorem conv_one (f : ℤ → M) : conv (1 : PowerSeries LL) f = f := by
  funext k
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem conv_zero_coeff (e : PowerSeries LL) (f : ℤ → M) (hf : ∀ k < (0 : ℤ), f k = 0) :
    conv e f 0 = PowerSeries.constantCoeff e • f 0 := by
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [hf _ (by omega), smul_zero]

theorem mem_latSpan {ι : Type} (ex : ι → ℤ → M) (x : ι) : ex x ∈ latSpan (LL := LL) ex :=
  Submodule.subset_span ⟨1, x, (conv_one _).symm⟩

theorem neg_eq_zero_of_std {ι : Type} {D : Submodule LL M} {ex : ι → ℤ → M}
    (h : Std D (latSpan (LL := LL) ex)) (x : ι) : ∀ k < (0 : ℤ), ex x k = 0 :=
  ((h _).1 (mem_latSpan ex x)).2

theorem full_of_std {D : Submodule LL M} {Λ : Submodule LL (ℤ → M)} (h : Std D Λ) : Full D Λ :=
  ⟨0, fun f h1 h2 => (h f).2 ⟨h1, by simpa using h2⟩⟩

theorem span_const_of_std {ι : Type} {D : Submodule LL M} {ex : ι → ℤ → M}
    (h : Std D (latSpan (LL := LL) ex)) :
    Submodule.span LL (Set.range fun x => ex x 0) = D := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ((h _).1 (mem_latSpan ex x)).1 0
  · intro d hd
    have h1 : (Pi.single (0 : ℤ) d : ℤ → M) ∈ latSpan (LL := LL) ex := by
      refine (h _).2 ⟨fun k => ?_, fun k hk => Pi.single_eq_of_ne hk.ne _⟩
      by_cases hk : k = 0
      · subst hk; simpa using hd
      · rw [Pi.single_eq_of_ne hk]; exact D.zero_mem
    have h2 : latSpan (LL := LL) ex ≤ (Submodule.span LL (Set.range fun x => ex x 0)).comap
        (LinearMap.proj (R := LL) (φ := fun _ : ℤ => M) 0) := by
      unfold latSpan
      rw [Submodule.span_le]
      rintro _ ⟨e, x, rfl⟩
      change conv e (ex x) 0 ∈ Submodule.span LL (Set.range fun x => ex x 0)
      rw [conv_zero_coeff e _ (neg_eq_zero_of_std h x)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    simpa using h2 h1

theorem exists_shift_of_std {D : Submodule LL M} {Λ : Submodule LL (ℤ → M)} (h : Std D Λ)
    (g : ℤ → M) (hg : g ∈ Λ) (h0 : g 0 = 0) : ∃ f ∈ Λ, ∀ j : ℤ, g j = f (j - ((1 : ℕ) : ℤ)) := by
  obtain ⟨h1, h2⟩ := (h g).1 hg
  refine ⟨fun j => g (j + 1), (h _).2 ⟨fun k => h1 _, fun k hk => ?_⟩, fun j => by simp⟩
  rcases (show k + 1 < 0 ∨ k + 1 = 0 by omega) with h3 | h3
  · exact h2 _ h3
  · rw [h3, h0]

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem prim_one (p : ℕ) : ∃ j : ℕ, IsPrimitiveRoot (1 : LL) (p ^ j) :=
  ⟨0, by simpa using IsPrimitiveRoot.one⟩

theorem sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem const_lev_π (i : ZMod n) : PowerSeries.constantCoeff (W.lev i 1 letπ) = 0 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π i 1 (prim_one _)
  have := congrArg PowerSeries.constantCoeff hE
  simpa [hE0] using this

theorem const_lev (i : ZMod n) (a : LetA O n) :
    PowerSeries.constantCoeff (W.lev i 1 a) = algebraMap O LL (PowerSeries.constantCoeff (a i)) := by
  obtain ⟨b, hb⟩ : (PowerSeries.X : PowerSeries O) ∣
      a i - PowerSeries.C (PowerSeries.constantCoeff (a i)) := by
    rw [PowerSeries.X_dvd_iff]; simp
  have h := W.lev_letter i 1
    (a - algebraMap O (LetA O n) (PowerSeries.constantCoeff (a i)) - letπ * fun _ => b) (by
      simp only [Pi.sub_apply, Pi.mul_apply, letπ, Pi.algebraMap_apply]
      rw [← hb]
      simp [PowerSeries.algebraMap_apply])
  rw [map_sub, map_sub, map_mul, AlgHom.commutes] at h
  have h2 := congrArg PowerSeries.constantCoeff h
  rw [map_sub, map_sub, map_mul, const_lev_π, zero_mul, sub_zero, map_zero, sub_eq_zero] at h2
  rw [h2]
  simp [PowerSeries.algebraMap_apply]

theorem const_lev_Q (i : ZMod n) : PowerSeries.constantCoeff (W.lev i 1 W.Q) = (PD.p : LL) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LevPt.Q_eq, map_sum, map_sum]
  simp [const_lev_π]

theorem π_dvd_of_van (hinj : Function.Injective (algebraMap O LL)) (a : LetA O n)
    (ha : ∀ i, a ∈ van W i 1 1) : (letπ : LetA O n) ∣ a := by
  have h : ∀ i, (PowerSeries.X : PowerSeries O) ∣ a i := by
    intro i
    have h1 := ha i
    rw [van, Ideal.mem_comap, Ideal.mem_span_singleton, pow_one, PowerSeries.X_dvd_iff,
      const_lev] at h1
    rw [PowerSeries.X_dvd_iff]
    exact hinj (by rw [h1, map_zero])
  choose b hb using h
  exact ⟨b, funext hb⟩

theorem cmp_eq_sum [NeZero n] (T : LocLat G Qp LL O) (x : ↥(W.N T)) :
    W.cmp T x = ∑ i : ZMod n, W.cmp T ((letE i : LetA O n) • x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← Finset.sum_smul, sum_letE, one_smul]

theorem cmp_iso_of_expansions [NeZero n] (hinj : Function.Injective (algebraMap O LL))
    (T : LocLat G Qp LL O) (ex : ZMod n → ↥(W.N T) → ℤ → T.V ⊗[Qp] B)
    (hcmp : ∀ i x, W.cmp T ((letE i : LetA O n) • x) = ex i x 0)
    (hstd : ∀ i, Std (DcrisL PD T.ρ (W.emb i)) (latSpan (LL := LL) (ex i)))
    (hsup : (⨆ i, DcrisL PD T.ρ (W.emb i)) = Dcris PD T.ρ)
    (hind : iSupIndep fun i => DcrisL PD T.ρ (W.emb i))
    {r : ℕ} (nb : Module.Basis (Fin r) (LetA O n) ↥(W.N T))
    (hvan : ∀ i (y : ↥(W.N T)), (∃ f ∈ latSpan (LL := LL) (ex i), ∀ j : ℤ,
      ex i y j = f (j - ((1 : ℕ) : ℤ))) → ∀ j, nb.repr y j ∈ van W i 1 1)
    (hφ : ∀ (i : ZMod n) (x : ↥(W.N T)) (m : ℕ) (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T),
      ex i ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ 0 =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i 1 (W.Q ^ m)) •
          (((PD.p : LL) ^ ((0 : ℤ) - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (ex (i - 1) x (0 - (j : ℤ))))) :
    GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison.CmpIso W PD.p T := by
  have hlet : ∀ i : ZMod n, Submodule.span LL
      (Set.range fun x : ↥(W.N T) => W.cmp T ((letE i : LetA O n) • x)) =
        DcrisL PD T.ρ (W.emb i) := by
    intro i
    simp only [hcmp]
    exact span_const_of_std (hstd i)
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, ?_, hlet, ?_⟩
  · rw [cmp_eq_sum] at hx
    have h0 : ∀ i, ex i x 0 = 0 := by
      intro i
      rw [← hcmp]
      exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 hind Finset.univ
        (fun i => W.cmp T ((letE i : LetA O n) • x)) (fun i _ => W.cmp_letter T i x) hx i
        (Finset.mem_univ _)
    have hv : ∀ j, (letπ : LetA O n) ∣ nb.repr x j := fun j =>
      π_dvd_of_van W hinj _ fun i =>
        hvan i x (exists_shift_of_std (hstd i) _ (mem_latSpan _ x) (h0 i)) j
    choose b hb using hv
    refine ⟨∑ j, b j • nb j, ?_⟩
    rw [Finset.smul_sum]
    conv_lhs => rw [← nb.sum_repr x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb j, mul_smul]
  · rintro ⟨y, rfl⟩
    exact W.cmp_π T y
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact W.cmp_mem T x
    · rw [← hsup, iSup_le_iff]
      intro i
      rw [← hlet i]
      apply Submodule.span_mono
      rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  · intro x m hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cmp_eq_sum W T x, cmp_eq_sum, map_sum, Finset.smul_sum,
      ← Equiv.sum_comp (Equiv.subRight (1 : ZMod n))
        (fun i => (PD.p : LL) ^ m •
          φVB PD (LL := LL) (V := T.V) (W.cmp T ((letE i : LetA O n) • x)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcmp, hcmp, Equiv.subRight_apply, hφ, finsum_eq_single _ 0]
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, map_pow, const_lev_Q]
      simp only [Nat.cast_zero, sub_zero, zpow_zero, one_smul]
    · intro j hj
      rw [neg_eq_zero_of_std (hstd (i - 1)) x (0 - (j : ℤ)) (by omega), map_zero, smul_zero,
        smul_zero]

end Generic


set_option maxHeartbeats 1000000 in
theorem cmp_iso (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison.CmpIso ((HW l).W K s LL h) ((D.loc l).PD K).p T := by
  have := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hstd := GlobalTheory.T.wach_lattice_eq_std_powerSeries_at_zero D HW F Cm l K s LL h T hT
  have hD := GlobalTheory.T.crystallineFrobenius_bijOn_letters_directSum D HW l K s LL h T hT
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  exact cmp_iso_of_expansions ((HW l).W K s LL h) Subtype.val_injective T
    (fun i => ex (Cm l) h T i 1) (fun i x => ((Cm l).C K s LL h).tie.cmp_eq T hT i x) hstd
    hD.2.1 hD.2.2.1 nb
    (fun i y => (((GlobalTheory.T.wachExpansion_basis_divisibility D HW F Cm l K s LL h T hT i 1 (prim_one l)
        (full_of_std (hstd i))).2 _ nb).2.2 y 1).1)
    (fun i x m hx => by
      have key := ((Cm l).C K s LL h).tie.levB_φ T hT i 1 (prim_one _) x m hx 0
      have h1 : (1 : ↥LL.1) ^ ((D.loc l).PD K).p = 1 := one_pow _
      simp only [h1] at key
      unfold ex
      exact key)

end GlobalTheory.NL.CmpCris
end
end

