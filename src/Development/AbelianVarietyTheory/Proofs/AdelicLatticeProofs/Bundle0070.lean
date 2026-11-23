module

public import Mathlib
public import Formalism.UnipotentAdelicQuotients.ThmBInHecke
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousBicharacterWeilSetup
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNontrivialHeckeChar
section
open HeckeCharacterZeroLocus.ThmBIn NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.HeckeInhabitant

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_fin : ∃ Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E, Continuous Φ ∧
    (∀ x, Φ (incA F E x) = algebraMap E _ x) ∧
    ∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v (Φ y P) ≤ 1 := by
  obtain ⟨ι, h1, h2, -⟩ := GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  refine ⟨ι.toRingHom.comp (finPart F E), ?_, fun x => h1 x, fun y => h2 _⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_
  have := GlobalTheory.HeckeTensorRead.continuous_of_map_integral
    (ι.toRingHom.comp (algebraMap (Af F) (Af F ⊗[F] E))) (fun a ha P =>
      (h2 (a ⊗ₜ[F] (1 : E))).1 (AddSubgroup.subset_closure ⟨a, ha, 1, rfl⟩) P)
  exact this.comp continuous_snd

theorem cA_inc (σ : E →ₐ[F] E) (x : E) : cA σ (incA F E x) = incA F E (σ x) := rfl

theorem val_alg (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (FiniteAdeleRing (𝓞 E) E) x P) = P.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x

end General

end GlobalTheory.HeckeInhabitant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacuumO
open GlobalTheory.FockCompare

variable {D : D7}

theorem map_fin_add {m n : ℕ} {x y : Mx D m n} (hx : x.map (finPart D) = 0) (hy : y.map (finPart D) = 0) :
    (x + y).map (finPart D) = 0 := by
  funext i j
  have e1 : finPart D (x i j) = 0 := congrFun (congrFun hx i) j
  have e2 : finPart D (y i j) = 0 := congrFun (congrFun hy i) j
  show finPart D (x i j + y i j) = 0
  rw [RingHom.map_add (f := _), e1, e2, add_zero]

theorem map_fin_neg {m n : ℕ} {x : Mx D m n} (hx : x.map (finPart D) = 0) : (-x).map (finPart D) = 0 := by
  funext i j
  have e1 : finPart D (x i j) = 0 := congrFun (congrFun hx i) j
  show finPart D (-x i j) = 0
  rw [RingHom.map_neg, e1, neg_zero]

def thick {m n : ℕ} (Λ : AddSubgroup (Mx D m n)) (N : ℕ) : AddSubgroup (Mx D m n) where
  carrier := {x | ∃ l ∈ Λ, (x - N • l).map (finPart D) = 0}
  zero_mem' := ⟨0, Λ.zero_mem, by
    funext i j
    show finPart D (((0 : Mx D m n) - N • (0 : Mx D m n)) i j) = 0
    rw [nsmul_zero, sub_zero]
    exact RingHom.map_zero _⟩
  add_mem' := by
    rintro x y ⟨l, hl, hx⟩ ⟨l', hl', hy⟩
    refine ⟨l + l', Λ.add_mem hl hl', ?_⟩
    have e : x + y - N • (l + l') = (x - N • l) + (y - N • l') := by rw [nsmul_add]; abel
    rw [e]
    exact map_fin_add hx hy
  neg_mem' := by
    rintro x ⟨l, hl, hx⟩
    refine ⟨-l, Λ.neg_mem hl, ?_⟩
    have e : -x - N • (-l) = -(x - N • l) := by rw [neg_nsmul]; abel
    rw [e]
    exact map_fin_neg hx

theorem piW_eq_zero (θ : InfFam D) (S T : HSp D) {u : WO S T} (hu : u.map (infPart D) = 0) : piW θ T S u = 0 := by
  funext τ i j
  have e : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
  show θ τ (infPart D (u i j)) = 0
  rw [e, RingHom.map_zero]

theorem lineAt_eq {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : Chart θ σ) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (v : RW T S) (h1 : v τ = z) (h2 : ∀ τ', τ' ≠ τ → v τ' = 0) (t : ℝ) :
    lineAt θ τ z t = iotaW σ T S (t • v) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hσ.inf _ _ τ z)
  refine hσ.real_ext (V := T) (W := S) (hL.2.1 t) (hσ.real_iota T S _) ?_
  rw [hσ.pi_iota]
  funext τ'
  refine (hL.2.2 t τ').trans ?_
  by_cases h : τ' = τ
  · rw [if_pos h, h, Pi.smul_apply, h1]
    funext i j
    exact (Complex.real_smul).symm
  · rw [if_neg h, Pi.smul_apply, h2 τ' h, smul_zero]
    rfl

theorem exists_ne_zero (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) :
    ∃ f : WO S T → ℂ, f ≠ 0 ∧ ∀ c : ℂ, IsThetaFunO ψ S T (fun w => c * f w) ∧
      IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) (fun w => c * f w) ∧
      ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (fun w => c * f w) := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨om, J, hom, hJ, halt, hJJ, hsym, hpos⟩ := _root_.GlobalTheory.OrientedRealForm.exists_real_form D ψ θ S T sS sT hψ hθ hS hT
  obtain ⟨aL, aR, a0, -, acont, arat, -, -, -⟩ := _root_.GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  obtain ⟨hinf, χ, c0, c1, c2, c3, c4, c5⟩ := _root_.GlobalTheory.SemiChar.exists_semichar D S T ΛS ΛT ψ hψ dS dT
  have htop : IsTopologicalAddGroup (WO S T) := (GlobalTheory.AdelicMatrixLattice.lattice D T S).1
  set Λ : AddSubgroup (WO S T) := latO S T ΛS ΛT fun _ => True with hΛ
  have hp2 : ∀ u ∈ Λ, piW θ T S (2 • u) = 0 := fun u hu => by
    rw [map_nsmul, piW_eq_zero θ S T (hinf u hu), smul_zero]
  have hlev : ∀ u ∈ thick Λ 2, ∃ l ∈ Λ, u - iotaW σ T S (piW θ T S u) = 2 • l := by
    rintro u ⟨l, hl, hu⟩
    refine ⟨l, hl, ?_⟩
    have e := hσ.iota_pi (V := T) (W := S) (x := u - 2 • l) hu
    rw [map_sub, hp2 l hl, sub_zero] at e
    rw [e]
    abel
  obtain ⟨f, f0, fc, fq, fl, fs, fv⟩ := _root_.GlobalTheory.HeisenbergGaussianSeries.exists_theta (WO S T) (RW T S) (piW θ T S) (iotaW σ T S)
    (fun x y => ψ (symplOH S T x y)) om J (ratL T S) (thick Λ 1) (thick Λ 2) χ
    (continuous_pi' hθ T S) (hσ.continuous_iota T S) (hσ.pi_iota T S)
    (fun x y z => by simp only [aL, AddChar.map_add_eq_mul])
    (fun x y z => by simp only [aR, AddChar.map_add_eq_mul])
    (fun x => by simp only [a0, AddChar.map_zero_eq_one])
    (fun x y => hψ.1.2.1 _) (hψ.1.1.comp acont)
    (fun x v => by
      have e := hom x (iotaW σ T S v) (hσ.real_iota T S v)
      rw [hσ.pi_iota] at e
      exact e)
    halt hJJ hsym hpos
    (fun g hg g' hg' => by
      obtain ⟨a, ha⟩ := arat g hg g' hg'
      simp only [ha]
      exact hψ.1.2.2.1 a)
    (by
      rintro _ ⟨g, rfl⟩ h
      have : g = 0 := by
        funext i j
        have e : θ (D.eTau.symm 1) (infPart D (incA D (g i j))) = 0 :=
          congrFun (congrFun (congrFun h (D.eTau.symm 1)) i) j
        rw [comp_incA hθ] at e
        exact (tauE D _).injective (e.trans (RingHom.map_zero _).symm)
      rw [this, map_zero])
    (fun v => ⟨0, Λ.zero_mem, by rw [nsmul_zero, sub_zero]; exact hσ.real_iota T S v⟩)
    (fun R => by
      refine ((_root_.GlobalTheory.CompletedLatticeFinite.finite_rational_points D S T ΛS ΛT dS dT R).image (ratW T S)).subset ?_
      rintro _ ⟨⟨g, rfl⟩, ⟨l, hl, h1⟩, h2⟩
      refine ⟨g, ⟨⟨l, hl, ?_⟩, fun τ i j => ?_⟩, rfl⟩
      · rw [one_nsmul] at h1
        exact h1
      · rw [← comp_incA hθ]
        let y : RW T S := piW θ T S (ratW T S g)
        exact ((norm_le_pi_norm (y τ i) j).trans ((norm_le_pi_norm (y τ) i).trans (norm_le_pi_norm y τ))).trans h2)
    (fun x hx => c0 x fun ⟨l, hl, h⟩ => hx ⟨l, hl, by rw [one_nsmul]; exact h⟩)
    c1 c2 (fun x v => c3 x _ (hσ.real_iota T S v))
    (_root_.GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT dS dT 2 two_pos)
    (fun u hu x => by
      obtain ⟨l, hl, e⟩ := hlev u hu
      rw [e]
      exact c4 l hl x)
  have hh : ∀ (c : ℂ) (u : WO S T), piW θ T S u = 0 → (∀ x, ψ (symplOH S T x u) * χ (x + u) = χ x) →
      heisO ψ S T u (fun w => c * f w) = fun w => c * f w := fun c u h1 h2 => by
    funext w
    show ψ (symplOH S T w u) * (c * f (w + u)) = c * f w
    rw [mul_left_comm, ← fl u h1 h2 w]
  refine ⟨f, f0, fun c => ⟨⟨fun g w => ?_, ⟨thick Λ 2, _root_.GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT dS dT 2 two_pos, fun u hu h => ?_⟩,
    continuous_const.mul fc, fun k L hL hL0 w => ?_⟩, ⟨fun u hu => hh c _ (hp2 u hu) (c4 u hu),
      fun e he u hu h => hh c u (piW_eq_zero θ S T (hinf u hu)) (c5 e he u hu h)⟩, fun τ z => ?_⟩⟩
  · have e : ψ (symplOH S T (ratW T S g) w) * f (ratW T S g + w) = f w := fq (ratW T S g) ⟨g, rfl⟩ w
    show c * f (ratW T S g + w) = _ * (c * f w)
    rw [← e, mul_left_comm, ← mul_assoc (ψ _), ← AddChar.map_add_eq_mul, neg_add_cancel,
      AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨l, hl, e⟩ := hlev u hu
    rw [piW_eq_zero θ S T h, map_zero, sub_zero] at e
    rw [e]
    exact hh c _ (hp2 l hl) (c4 l hl)
  · exact contDiff_const.mul (((smooth_iff_sm_and_real_lines D θ σ hσ T S).1 f).2 fs k L hL hL0 w)
  · funext w
    let v : RW T S := Pi.single τ z
    have v1 : v τ = z := Pi.single_eq_same _ _
    have v2 : ∀ τ', τ' ≠ τ → v τ' = 0 := fun τ' h => Pi.single_eq_of_ne h _
    have l1 := lineAt_eq hσ S T τ z v v1 v2
    have l2 := lineAt_eq hσ S T τ (cplxO (sS τ) (sT τ) z) (J v) (by rw [hJ, v1]) (fun τ' h => by
      rw [hJ, v2 τ' h]
      have : cplxO (sS τ') (sT τ') (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ) = 0 := by simp [cplxO]
      exact this)
    have e := fv w v
    show deriv (fun t : ℝ => ψ (symplOH S T w (lineAt θ τ z t)) * (c * f (w + lineAt θ τ z t))) 0 +
      Complex.I * deriv (fun t : ℝ => ψ (symplOH S T w (lineAt θ τ (cplxO (sS τ) (sT τ) z) t)) *
        (c * f (w + lineAt θ τ (cplxO (sS τ) (sT τ) z) t))) 0 = 0
    simp only [l1, l2, mul_left_comm _ c, deriv_const_mul_field']
    rw [← mul_add]
    exact mul_eq_zero_of_right c e

theorem vacExists : ∀ D : D7, VacExistsO D := by
  intro D ψ θ hψ hθ S T sS sT _ _ hS hT ΛS ΛT dS dT
  obtain ⟨f, f0, hf⟩ := exists_ne_zero ψ θ hψ hθ S T sS sT hS hT ΛS ΛT dS dT
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  let _ : MeasurableSpace (WO S T) := measMx _ _
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have h1 := (hf 1).1
  simp only [one_mul] at h1
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := _root_.GlobalTheory.exists_normalise_meanSquare_of_cocompact (WO S T) (ratL T S) K hK hcov f h1.cont f0 (by
    rintro _ ⟨g, rfl⟩ w
    have e := h1.quasi g w
    have e' := congrArg norm e
    rw [norm_mul, hψ.1.2.1, one_mul] at e'
    exact e')
  exact ⟨fun w => c * f w, hψ, hθ, (hf c).1, (hf c).2.1, (hf c).2.2, ⟨(μ, 𝓕), hμ⟩,
    fun p hp => hc p.1 p.2 hp.1 hp.2.1 hp.2.2⟩

end GlobalTheory.VacuumO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitScalar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem idem_smul_mem {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {e : AE D}
    (he : e * e = e) : ∀ u ∈ latO S T LS LT fun _ => True, e • u ∈ latO S T LS LT fun _ => True :=
  GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ e
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he]))

theorem off_smul_mt {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    (1 - (e + cA D e)) • mt V g = (1 - (e + cA D e)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : (e + cA D e) • (mt V g - 1) = mt V g - 1 := Matrix.ext fun i j => hg i j
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, h, sub_self]

theorem off_smul_mt_inv {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    (1 - (e + cA D e)) • mt V g⁻¹ = (1 - (e + cA D e)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : mt V g * mt V g⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [← h, ← Matrix.smul_mul, off_smul_mt hg, Matrix.smul_mul, Matrix.one_mul]

theorem off_smul_actO {e : AE D} {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) (u : WO S T) :
    (1 - (e + cA D e)) • actO S T g h u = (1 - (e + cA D e)) • u := by
  unfold actO
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, off_smul_mt hh, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul,
    ← Matrix.mul_smul, off_smul_mt_inv hg, Matrix.mul_smul, Matrix.mul_one]

theorem compAt_mt {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} (hg : SuppAt e V g) (θ : InfFam D)
    (τ : D.what₂.Tau) : compAt θ τ (mt V g) = 1 := by
  refine Matrix.ext fun i j => ?_
  have h : infPart D ((mt V g - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add (f := _), infPart_splitIdem he,
      infPart_splitIdem (isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show θ τ (infPart D (mt V g i j)) = _
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one, RingHom.map_one]
  · rw [RingHom.map_zero, RingHom.map_zero]

theorem pairNorm_smul {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (c : ℝ) (f : Mx D m n → ℂ) :
    nrm2 μ 𝓕 ((c : ℂ) • f) = c ^ 2 * nrm2 μ 𝓕 f := by
  unfold nrm2
  rw [← integral_const_mul]
  congr 1
  funext w
  rw [Pi.smul_apply, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem reps_eq {Λ Λ' : AddSubgroup (WO S T)} {e : AE D} {R : Finset (WO S T)}
    (hR : ∀ u ∈ R, u ∈ Λ' ∧ IsHalf e u) (hRu : ∀ u ∈ Λ', IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ Λ)
    {u v : WO S T} (hu : u ∈ R) (hv : v ∈ R) (h : u - v ∈ Λ) : u = v :=
  (hRu u (hR u hu).1 (hR u hu).2).unique ⟨hu, by rw [sub_self]; exact zero_mem _⟩ ⟨hv, h⟩

theorem sum_sub_notMem {Λ Λ' : AddSubgroup (WO S T)} {e : AE D} (he : IsSplitIdem D e)
    (hst : ∀ u ∈ Λ, e • u ∈ Λ) (hstc : ∀ u ∈ Λ, cA D e • u ∈ Λ) {R R' : Finset (WO S T)}
    (hR : ∀ u ∈ R, u ∈ Λ' ∧ IsHalf e u) (hRu : ∀ u ∈ Λ', IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ Λ)
    (hR' : ∀ u ∈ R', u ∈ Λ' ∧ IsHalf (cA D e) u) (hRu' : ∀ u ∈ Λ', IsHalf (cA D e) u → ∃! v, v ∈ R' ∧ u - v ∈ Λ)
    {u v u' v' : WO S T} (hu : u ∈ R) (hv : v ∈ R) (hu' : u' ∈ R') (hv' : v' ∈ R') (hne : (u, u') ≠ (v, v')) :
    u + u' - (v + v') ∉ Λ := by
  intro hmem
  have e1 : u + u' - (v + v') = (u - v) + (u' - v') := by abel
  have a1 := (isHalf_iff _ _).1 (isHalf_sub (hR _ hu).2 (hR _ hv).2)
  have a2 := (isHalf_iff _ _).1 (isHalf_sub (hR' _ hu').2 (hR' _ hv').2)
  have b1 : e • (u' - v') = 0 := by rw [← a2, smul_smul, he.2.1, zero_smul]
  have b2 : cA D e • (u - v) = 0 := by rw [← a1, smul_smul, mul_comm, he.2.1, zero_smul]
  have c1 := hst _ hmem
  have c2 := hstc _ hmem
  rw [e1, smul_add, a1, b1, add_zero] at c1
  rw [e1, smul_add, a2, b2, zero_add] at c2
  exact hne (by rw [reps_eq hR hRu hu hv c1, reps_eq hR' hRu' hu' hv' c2])

theorem form_sum {Λ Λ' : AddSubgroup (WO S T)} {e : AE D} (he : IsSplitIdem D e)
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hdd : ∀ u ∈ Λ', ∀ u' ∈ Λ', ψ (symplO S T u u') = 1)
    (hstc : ∀ u ∈ Λ, cA D e • u ∈ Λ) {R R' : Finset (WO S T)}
    (hR : ∀ u ∈ R, u ∈ Λ' ∧ IsHalf e u) (hRu : ∀ u ∈ Λ', IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ Λ)
    (hR' : ∀ u ∈ R', u ∈ Λ' ∧ IsHalf (cA D e) u) {f : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) Λ f)
    (hth : ∀ u : WO S T, IsHalf e u → IsThetaFunO ψ S T (heisO ψ S T u f)) {ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ}
    (hℓ : ∀ y, IsHalf (cA D e) y → ∀ φ, IsThetaFunO ψ S T φ → ℓ (heisO ψ S T y φ) = ℓ φ) :
    ℓ (∑ u ∈ R, ∑ u' ∈ R', heisO ψ S T u (heisO ψ S T u' f)) = R'.card * ℓ f := by
  have he' := isSplitIdem_conj he
  obtain ⟨v₀, ⟨hv₀, hv₀Λ⟩, hv₀u⟩ := hRu 0 (zero_mem _) (isHalf_zero e)
  have h1 : ∀ u ∈ R, ℓ (∑ u' ∈ R', heisO ψ S T u (heisO ψ S T u' f)) = R'.card * ℓ (heisO ψ S T u f) := by
    intro u hu
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun u' hu' => ?_
    rw [heisO_comm, hdd _ (hR u hu).1 _ (hR' u' hu').1, one_smul, hℓ _ (hR' u' hu').2 _ (hth u (hR u hu).2)]
  have hv₀' : v₀ ∈ Λ := by rwa [zero_sub, neg_mem_iff] at hv₀Λ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl h1, Finset.sum_eq_single_of_mem v₀ hv₀, hf.2 e he v₀ hv₀' (hR _ hv₀).2]
  intro u hu hne
  have huΛ : u ∉ Λ := fun huΛ => hne (hv₀u u ⟨hu, by rwa [zero_sub, neg_mem_iff]⟩)
  obtain ⟨l, hl, hlh, hlne⟩ := exists_dual_half he hd hstc (hR u hu).2 huΛ
  have h2 := hℓ l hlh _ (hth u (hR u hu).2)
  rw [heisO_comm, hf.2 _ he' l hl hlh, map_smul, smul_eq_mul] at h2
  have h3 : (ψ (symplO S T l u) - 1) * ℓ (heisO ψ S T u f) = 0 := by rw [sub_mul, h2, one_mul, sub_self]
  rw [(mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hlne), mul_zero]

theorem om_vacuum_eq_splitFac_smul_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC S ΛS' → IsSelfDualC T ΛT → IsSelfDualC T ΛT' → ∀ (e : AE D), IsSplitIdem D e → ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → (∀ u : WO S T, u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u = actO S T g h u₀) → ∀ (R R' : Finset (WO S T)), (∀ u ∈ R, u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ IsHalf e u) → (∀ u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → (∀ u ∈ R', u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ IsHalf (cA D e) u) → (∀ u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf (cA D e) u → ∃! v, v ∈ R' ∧ u - v ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ f, IsVacO ψ θ S T sS sT ΛS ΛT f → om (g, h) f = ((splitFacO χS χT x y : ℂ) * ((Real.sqrt ((R.card : ℝ) * R'.card) : ℝ) : ℂ)⁻¹) • ∑ u ∈ R, ∑ u' ∈ R', heisO ψ S T u (heisO ψ S T u' f) := by
  intro D ψ θ S T χS χT om hW hθ hS hT sS sT hsS hsT ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT' e he g h hg hh x y hx hy hmove
    R R' hR hRu hR' hRu' f hf
  classical
  have he' := isSplitIdem_conj he
  have hψ := hW.std
  obtain ⟨hd, -, hsign⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hΛS hΛT
  obtain ⟨hd', -, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS' ΛT' hψ hΛS' hΛT'
  have hom := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ g h
    (fun τ => by rw [compAt_mt he hg, mul_one, one_mul]) (fun τ => by rw [compAt_mt he hh, mul_one, one_mul])
    hmove f hf
  have hst := @idem_smul_mem D S T ΛS ΛT _ he.1
  have hstc := @idem_smul_mem D S T ΛS ΛT _ he'.1
  have hst' := @idem_smul_mem D S T ΛS' ΛT' _ he.1
  have hstc' := @idem_smul_mem D S T ΛS' ΛT' _ he'.1
  have hfin' := @latO_fin D S T ΛS' ΛT'
  have huniq := fun F (hF : IsVacO ψ θ S T sS sT ΛS' ΛT' F) =>
    GlobalTheory.VacUnique.vacUniqueO D ψ θ hψ hθ S T sS sT hS hT hsS hsT ΛS' ΛT' hΛS' hΛT' F _ hF hom
  obtain ⟨-, hf⟩ := hf
  unfold IsVacO at huniq
  generalize (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) = Λ at *
  generalize (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) = Λ'
    at *
  have hdd : ∀ u ∈ Λ', ∀ u' ∈ Λ', ψ (symplO S T u u') = 1 := fun u hu => (hd' u (hfin' hu)).1 hu
  have hoff : ∀ u ∈ Λ', (1 - (e + cA D e)) • u ∈ Λ := by
    intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := (hmove u).1 hu
    rw [off_smul_actO hg hh, sub_smul, add_smul, one_smul]
    exact sub_mem hu₀ (add_mem (hst _ hu₀) (hstc _ hu₀))
  obtain ⟨F, hFdef⟩ : ∃ F, F = ∑ u ∈ R, ∑ u' ∈ R', heisO ψ S T u (heisO ψ S T u' f) := ⟨_, rfl⟩
  rw [← hFdef]
  have hFlat : IsLatVac (heisO ψ S T) Λ' F := hFdef ▸ isLatVac_sum he hdd hst' hstc' hoff hR hRu hR' hRu' hf.lat
  have hF : F = ∑ p ∈ R ×ˢ R', ψ (symplOH S T p.1 p.2) • heisO ψ S T (p.1 + p.2) f := by
    rw [Finset.sum_product]
    simp only [hFdef, heisO_heisO]
  have hafin : ∀ p ∈ R ×ˢ R', (p.1 + p.2).map (infPart D) = 0 := fun p hp =>
    hfin' (add_mem (hR _ (Finset.mem_product.1 hp).1).1 (hR' _ (Finset.mem_product.1 hp).2).1)
  obtain ⟨v₀, ⟨hv₀, -⟩, -⟩ := hRu 0 (zero_mem _) (isHalf_zero e)
  obtain ⟨v₁, ⟨hv₁, -⟩, -⟩ := hRu' 0 (zero_mem _) (isHalf_zero _)
  have hcR : (0 : ℝ) < R.card := Nat.cast_pos.2 (Finset.card_pos.2 ⟨v₀, hv₀⟩)
  have hcR' : (0 : ℝ) < R'.card := Nat.cast_pos.2 (Finset.card_pos.2 ⟨v₁, hv₁⟩)
  have hN : 0 < (R.card : ℝ) * R'.card := mul_pos hcR hcR'
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (Real.sqrt ((R.card : ℝ) * R'.card))⁻¹ := ⟨_, rfl⟩
  have ht0 : 0 < t := ht ▸ inv_pos.2 (Real.sqrt_pos.2 hN)
  have htF : (t : ℂ) • F = ∑ p ∈ R ×ˢ R', ((t : ℂ) * ψ (symplOH S T p.1 p.2)) • heisO ψ S T (p.1 + p.2) f := by
    rw [hF, Finset.smul_sum]
    simp only [smul_smul]
  have hnorm : ∀ μ 𝓕, IsCovolOne (ratL T S) μ 𝓕 → nrm2 μ 𝓕 F = (R.card : ℝ) * R'.card := by
    intro μ 𝓕 hμ
    rw [hF, GlobalTheory.HeisOrtho.thetaNormSq_sum_heisenbergTranslates_distinctChars D ψ S T hψ.1 μ 𝓕 hμ f hf.theta (hf.norm.2 (μ, 𝓕) hμ) _ _ _ _
      (fun p _ => hψ.1.2.1 _) ?_, Finset.card_product, Nat.cast_mul]
    rintro ⟨u, u'⟩ hp ⟨v, v'⟩ hq hne
    obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
    obtain ⟨hv, hv'⟩ := Finset.mem_product.1 hq
    have hm : u + u' - (v + v') ∈ Λ' :=
      sub_mem (add_mem (hR _ hu).1 (hR' _ hu').1) (add_mem (hR _ hv).1 (hR' _ hv').1)
    have hnot : u + u' - (v + v') ∉ Λ := sum_sub_notMem he hst hstc hR hRu hR' hRu' hu hv hu' hv' hne
    rw [hd _ (hfin' hm)] at hnot
    push Not at hnot
    obtain ⟨l, hl, hne'⟩ := hnot
    obtain ⟨ε, hε, hεf⟩ := hsign f hf.lat l hl
    exact ⟨l, ε, by rcases hε with rfl | rfl <;> simp, hεf f hf.lat, hne'⟩
  obtain ⟨c, hc, hcF⟩ := huniq ((t : ℂ) • F) ⟨hψ,
    { inf := hθ
      theta := htF ▸ GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 f hf.theta _ _ _ _ hafin
      lat := ⟨fun u hu => by rw [heisO_smul, hFlat.1 u hu],
        fun e₁ he₁ u hu hue => by rw [heisO_smul, hFlat.2 e₁ he₁ u hu hue]⟩
      fock := fun τ => htF ▸ GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ.1 hθ f hf.theta τ _ (hf.fock τ) _ _ _ _ hafin
      norm := ⟨hf.norm.1, fun p hp => by
        beta_reduce
        rw [pairNorm_smul, hnorm _ _ hp, ht, inv_pow, Real.sq_sqrt hN.le, inv_mul_cancel₀ hN.ne']⟩ }⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp⟩ := hf.norm.1
    have := hf.norm.2 p hp
    simp [nrm2] at this
  obtain ⟨ℓ, hℓ0, hℓ⟩ := exists_invariant_form he' hd
    (by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hst) hf0 hf.lat
  obtain ⟨r, hr, hrℓ⟩ := hW.om_split e he g h hg hh x y hx hy
  have hval := hrℓ ℓ (fun u hu φ hφ => hℓ u hu φ hφ) f hf.theta
  have hth : ∀ u : WO S T, IsHalf e u → IsThetaFunO ψ S T (heisO ψ S T u f) := by
    intro u hu
    have := GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 f hf.theta Unit {()} (fun _ => u) (fun _ => 1) fun _ _ => half_fin he hu
    rwa [Finset.sum_singleton, one_smul] at this
  have hℓF : ℓ F = R'.card * ℓ f := hFdef ▸ form_sum he hd hdd hstc hR hRu hR' hf.lat hth hℓ
  rw [hcF, map_smul, map_smul, hℓF, smul_eq_mul, smul_eq_mul] at hval
  have h4 : c * ((t * R'.card : ℝ) : ℂ) = (r : ℂ) * (splitFacO χS χT x y : ℂ) := by
    apply mul_right_cancel₀ hℓ0
    rw [← hval]
    push_cast
    ring
  have h5 : t * R'.card = r := by
    have := congrArg norm h4
    rwa [norm_mul, norm_mul, hc, Circle.norm_coe, one_mul, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (mul_pos ht0 hcR').le, Real.norm_of_nonneg hr.le] at this
  rw [h5, mul_comm] at h4
  have h6 : c = splitFacO χS χT x y := mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne') h4
  rw [hcF, h6, smul_smul, ht, Complex.ofReal_inv]

end GlobalTheory.SplitScalar

end
end

