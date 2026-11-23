module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormMapOfFinOrder
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0089
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerInfConjIntegralGLProdLeCptPartStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_inf_conj_integralGLProd_le_cptPart : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E) (m q : GLw a w × GLw b w), twCent (MonoidHom.id _) m ⊓ ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))).map (MulAut.conj q).toMonoidHom ≤ cptPart (twCent (MonoidHom.id _) m) := by
  first | exact @GlobalTheory.CentCpt.twCent_inf_conjKK_le_cptPart | exact GlobalTheory.CentCpt.twCent_inf_conjKK_le_cptPart | (intros; apply GlobalTheory.CentCpt.twCent_inf_conjKK_le_cptPart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicCommStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_regular_rationalPoint_finiteAdelic_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n), γ.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ), ∀ b ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ), a * b = b * a := by
  first | exact @GlobalTheory.BCT.finCent_comm | exact GlobalTheory.BCT.finCent_comm | (intros; apply GlobalTheory.BCT.finCent_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFirst
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ScalarModulus

theorem norm_eq_one_of_locK {X : Fields} {Pr : Primes X} {m : ℕ} {Ch : Chars X Pr m} {σ₀ : X.K →+* ℂ} {e : X.Tau → ℚ}
    {j : Fin m} {χ : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (h : GlobalTheory.Mem.Chr.IsMu0 Ch σ₀ e j χ)
    (P : HeightOneSpectrum (𝓞 X.E)) (x : X.Eˣ) (y : X.K) (hy : σ₀ y = ((χ.locK P x : ℂˣ) : ℂ)) (σ : X.K →+* ℂ) :
    ‖σ y‖ = 1 := by
  have h0 : ((Pr.g 0 : ℕ) : 𝓞 X.E) * ((Pr.g 1 : ℕ) : 𝓞 X.E) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (hPr.g_prime 0).ne_zero) (by exact_mod_cast (hPr.g_prime 1).ne_zero)
  obtain ⟨M, z, hM, -, -, hz⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf X.E χ
    (divs (((Pr.g 0 : ℕ) : 𝓞 X.E) * ((Pr.g 1 : ℕ) : 𝓞 X.E))) (GlobalTheory.CharVal.productRule χ)
    (fun v hv => h.unr v fun i hi => hv ((Formalism.L2.Col.mem_divs h0 v).2 (by
      fin_cases i
      exacts [v.asIdeal.mul_mem_right _ hi, v.asIdeal.mul_mem_left _ hi]))) h.tame P x
  obtain ⟨n, -, hn⟩ := h.inf
  have hz' := congrArg Units.val hz
  rw [Units.val_mul, Units.val_pow_eq_pow_val, hn z, ← hy, Units.val_one] at hz'
  have hsq : ∀ τ, (X.embC σ₀ τ (z : X.E) / ((‖X.embC σ₀ τ (z : X.E)‖ : ℝ) : ℂ)) ^ 2 =
      σ₀ (X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) := by
    intro τ
    have h1 : X.embC σ₀ τ z ≠ 0 := (map_ne_zero _).2 z.ne_zero
    have h2 := hX.conjE (X.embC σ₀ τ) z
    rw [map_div₀]
    change _ = X.embC σ₀ τ z / X.embC σ₀ τ (star (z : X.E))
    rw [h2, div_pow, ← Complex.mul_conj', pow_two, mul_div_mul_left _ _ h1]
  have key : y ^ (M * 2) * ∏ τ, (X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) ^ n τ = 1 := by
    apply σ₀.injective
    rw [map_one, map_mul, map_pow, map_prod, pow_mul]
    have h3 : ∏ τ, σ₀ ((X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) ^ n τ) =
        (∏ τ, (X.embC σ₀ τ (z : X.E) / ((‖X.embC σ₀ τ (z : X.E)‖ : ℝ) : ℂ)) ^ n τ) ^ 2 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_zpow₀, ← hsq, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [h3, ← mul_pow, hz', one_pow]
  have h4 : ‖σ (∏ τ, (X.emb τ (z : X.E) / X.emb τ (star (z : X.E))) ^ n τ)‖ = 1 := by
    rw [map_prod, norm_prod]
    refine Finset.prod_eq_one fun τ _ => ?_
    have h1 : ‖(σ.comp (X.emb τ)) z‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero _).2 z.ne_zero)
    have h2 := hX.conjE (σ.comp (X.emb τ)) z
    rw [RingHom.comp_apply] at h1
    rw [RingHom.comp_apply, RingHom.comp_apply] at h2
    rw [map_zpow₀, norm_zpow, map_div₀, norm_div, h2, Complex.norm_conj, div_self h1, one_zpow]
  have h5 := congrArg (fun t => ‖σ t‖) key
  simp only [map_mul, map_pow, norm_mul, norm_pow, h4, mul_one, map_one, norm_one] at h5
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h5

theorem norm_muInvDet {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel)
    (hS : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs)
    (ht : Ch.Tied G.σ₀ e G.mu0 eta) (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} (hj : j < R.m) {n : ℕ}
    (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)) (σ : X.K →+* ℂ) :
    ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu j) (muAt Ch sel mu cst j) N fr)‖ = 1 := by
  have hU := fun P x y hy => norm_eq_one_of_locK hX hPr (ht.mu0 ⟨j, hj⟩) P x y hy σ
  have hval : ∀ P : HeightOneSpectrum (𝓞 X.E), (∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.asIdeal) →
      ‖σ (Ch.muVal ⟨j, hj⟩ P : X.K)‖ = 1 := fun P hP =>
    hU P (Formalism.L2.Host.unif P) _ (ht.muVal _ P hP)
  have hfin := GlobalTheory.CharVal.finOrder_tup mu
  have h1 : ∀ P : rowSG Pr sel mu, ‖σ (cst.muq (j + 1) P)‖ = 1 := by
    intro P
    have hq : ‖σ ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K)‖ = 1 :=
      GlobalTheory.GO.norm_map_of_finOrder _ (GlobalTheory.CharVal.finOrder_qVal hfin P.1)
    have h1 := hL.muqG j hj P (hS P) (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) rfl
    have h2 : G.σ₀ ((cst.muq (j + 1) P * ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K))⁻¹) =
        (((G.mu0 ⟨j, hj⟩).locK P.1 (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) : ℂˣ) : ℂ) := by
      rw [map_inv₀, map_mul, h1, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one, inv_inv]
    have h3 := hU P.1 _ _ h2
    rwa [map_inv₀, map_mul, norm_inv, norm_mul, hq, mul_one, inv_eq_one] at h3
  have h2 : ‖σ (muOff sel (rowSG Pr sel mu) (mUof Ch mu j) N)‖ = 1 := by
    unfold muOff
    refine finprod_induction (fun x => ‖σ x‖ = 1) (by simp)
      (fun x y hx hy => by rw [map_mul, norm_mul, hx, hy, one_mul]) fun v => ?_
    split_ifs with hv
    · simp
    · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, norm_zpow, mUof, dite_eq_left hj, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, norm_mul, norm_inv, norm_inv,
        hval _ (GlobalTheory.ColPeriod.Scal.g_notMem_sel hX hPr hsel hv),
        GlobalTheory.GO.norm_map_of_finOrder _ (GlobalTheory.CharVal.finOrder_unifVal hfin _)]
      simp
  rw [muInvDet, map_mul, norm_mul, h2, one_mul, map_prod, norm_prod]
  refine Finset.prod_eq_one fun P _ => ?_
  unfold muAt
  obtain ⟨z, ζ, hζ, e⟩ := GlobalTheory.LocCharVal.locChar_eq_zpow_mul X.E X.K P.1 (qOf P.1) (cst.muq (j + 1) P) _
    ((LinearEquiv.det (fr P) : X.Eˣ) : X.E)
    (GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _)
      (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P).1.2) (Units.ne_zero _)
  rw [e, map_mul, map_zpow₀, norm_mul, norm_zpow, h1, GlobalTheory.GO.norm_map_of_finOrder _ hζ, one_zpow, one_mul]

end GlobalTheory.ScalarModulus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralTopIndependentOfSmoothWeight
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernMass

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {L : LB X}

theorem sub_pick_eq (φ ψ : Weight p σ L) {y : CxPts p σ} {i : L.ι} (hi : y ∈ ptsIn p σ (L.U i)) :
    ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y = ψ.φ i y - φ.φ i y := by
  rw [ψ.trans _ i y (mem_pick φ.isLB y) hi, φ.trans _ i y (mem_pick φ.isLB y) hi]
  ring

theorem cInfAt_half_sub {φ ψ : Weight p σ L} (hφ : φ.IsCInf) (hψ : ψ.IsCInf) (x : CxPts p σ) :
    CInfAt (fun y => (ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y) / 2) x := by
  have hx := mem_pick φ.isLB x
  refine (((hψ _ x hx).add (hφ _ x hx).neg).const_mul 2⁻¹).congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds hx] with z hz
  rw [sub_pick_eq φ ψ hz]
  ring

theorem mInt_one_eq {D : ℕ} [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    {A : FinHolAtlas D (CxPts p σ)} (hA : IsAlgAtlas A) {φ ψ : Weight p σ L} (hφ : φ.IsCInf)
    (hψ : ψ.IsCInf) :
    mInt A (fun _ => φ.locPot) (fun _ => 1) = mInt A (fun _ => ψ.locPot) (fun _ => 1) := by
  have hP : IsPotential A φ.locPot :=
    ((Weight.isCInf_iff_isSmooth hA.anRead).1 hφ).isPotential hA
  have hu : A.Smooth fun y => (ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y) / 2 :=
    (hA.smooth_iff hA.anRead).2 ((cInfAt_iff_smoothOn hA.anRead isOpen_univ).1
      fun y _ => cInfAt_half_sub hφ hψ y)
  rw [← massIndep A (fun _ => φ.locPot) (fun _ => _) (fun _ => hP) fun _ => hu]
  refine SameForm.mInt_eq (fun _ j y hy => hessCGerm _ _ _ ?_) _
  refine eventually_of_mem (((A.chart j).isOpen_inter_preimage_symm (isOpen_ptsIn _)).mem_nhds
    ⟨hy, mem_pick φ.isLB ((A.chart j).symm y)⟩) fun w hw => ?_
  change φ.φ _ _ / 2 + (_ - _) / 2 = ψ.φ (pick φ.isLB _) _ / 2
  rw [sub_pick_eq φ ψ hw.2]
  ring

theorem chernInt_one_eq : ∀ (Y : Var ℂ) (L : LB Y.X) (φ ψ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := fun Y L φ ψ hφ hψ => by
  obtain ⟨h₁, h₂, -, A, hA⟩ := _root_.GlobalTheory.cxPts_var_compact_manifold Y
  rw [(_root_.GlobalTheory.chernInt_one_eq_mInt Y L φ hφ).2 A hA, (_root_.GlobalTheory.chernInt_one_eq_mInt Y L ψ hψ).2 A hA]
  exact mInt_one_eq hA hφ hψ

end GlobalTheory.ChernMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiDeltaUConjLongSimpleReflectionUnitary
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory

namespace GKUnitary

theorem diag_conj_weylRep {R : Type} [CommRing R] {n : ℕ} {s : Equiv.Perm (Fin n)} {y t : GL (Fin n) R}
    (hy : IsWeylRep s y) (ht : ∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) R) i j = 0) (i : Fin n) :
    ((y⁻¹ * t * y : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i i =
      (t : Matrix (Fin n) (Fin n) R) (s i) (s i) := by
  have h1 : ((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (s i) * (y : Matrix (Fin n) (Fin n) R) (s i) i = 1 := by
    have h := congrFun (congrFun (Units.inv_mul y) i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single (s i)] at h
    · rw [h, Matrix.one_apply_eq]
    · intro b _ hb; rw [hy b i hb, mul_zero]
    · simp
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (s i)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
    · calc ((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (s i) * (t : Matrix (Fin n) (Fin n) R) (s i) (s i) *
            (y : Matrix (Fin n) (Fin n) R) (s i) i
          = (t : Matrix (Fin n) (Fin n) R) (s i) (s i) *
            (((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (s i) * (y : Matrix (Fin n) (Fin n) R) (s i) i) := by ring
        _ = _ := by rw [h1, mul_one]
    · intro b _ hb; rw [ht b (s i) hb, mul_zero]
    · simp
  · intro b _ hb; rw [hy b i hb, mul_zero]
  · simp

theorem ordL_congr {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x y : L}
    (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  have key : ∀ z : L, ordL z = (fun w : WithZero (Multiplicative ℤ) =>
      if h : w = 0 then (0 : ℤ) else -Multiplicative.toAdd (WithZero.unzero h)) (Valued.v z) := fun _ => rfl
  rw [key x, key y, h]

theorem ordL_one' {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] : ordL (1 : L) = 0 :=
  Formalism.UG.P.fIwasawa_ordL_unit 1 1 (by simp) (by simp) (by simp)

theorem chiDeltaU_conj_simpleU_long :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n →
    ∀ (y : GU σ n), IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (α : Fin (n / 2) → ℂˣ) (t : GU σ n),
    (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
    chiDeltaU q (fun i => (α i : ℂ)) (y⁻¹ * t * y) *
        (q : ℂ) ^ (-2 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
      chiDeltaU q (fun i => (actU k α i : ℂ)) t := by
  intro L _ _ ϖ σ q hU n k hk hn y hy α t ht
  obtain ⟨hσ, hσv, -, -, -, hq2, -⟩ := hU
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  have hact : actU k α = Function.update α k (α k)⁻¹ := by simp [actU, hk]
  obtain ⟨m, hm⟩ := hn
  have hkv : k.val + 1 = m := by have := k.2; omega
  have hrev : ((lo k).rev : ℕ) = m := by simp [Fin.val_rev, lo]; omega
  set T : Matrix (Fin n) (Fin n) L := ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hT
  have hdiag : ∀ i, (((y⁻¹ * t * y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      T (simpleU k i) (simpleU k i) := by
    intro i
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact diag_conj_weylRep hy ht i

  have hprod : σ (T (lo k).rev (lo k).rev) * T (lo k) (lo k) = 1 := by
    have hu := (GlobalTheory.LGrp.mem_GU_iff σ n (t : GL (Fin n) L)).1 t.2 (lo k) (lo k)
    have h := congrFun (congrFun (Units.inv_mul (t : GL (Fin n) L)) (lo k)) (lo k)
    rw [Matrix.mul_apply, Finset.sum_eq_single (lo k)] at h
    · rw [← hu, h, Matrix.one_apply_eq]
    · intro b _ hb; exact mul_eq_zero_of_right _ (ht b (lo k) hb)
    · simp
  have ha0 : T (lo k) (lo k) ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hb0 : σ (T (lo k).rev (lo k).rev) ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hord : ordL (T (lo k).rev (lo k).rev) = -ordL (T (lo k) (lo k)) := by
    have h := Formalism.UG.P.fIwasawa_ordL_mul _ _ hb0 ha0
    rw [hprod, ordL_one', ordL_congr (hσv _)] at h
    omega
  unfold chiDeltaU
  rw [← hT]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  have hrest : ∀ i ∈ Finset.univ.erase k,
      (if h : i.val < n then (α i : ℂ) ^ ordL ((((y⁻¹ * t * y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩) *
        (q : ℂ) ^ (-(ordL ((((y⁻¹ * t * y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩)) *
          ((n : ℤ) - 1 - 2 * (i.val : ℤ))) else 1) =
      (if h : i.val < n then (actU k α i : ℂ) ^ ordL (T ⟨i.val, h⟩ ⟨i.val, h⟩) *
        (q : ℂ) ^ (-(ordL (T ⟨i.val, h⟩ ⟨i.val, h⟩)) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))) else 1) := by
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hin : i.val < n := by have := i.2; omega
    rw [dite_eq_left hin, dite_eq_left hin, hdiag, hact, Function.update_of_ne hik]
    have hfix : simpleU k ⟨i.val, hin⟩ = ⟨i.val, hin⟩ := by
      rw [hs]
      refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
      · intro h; apply hik; ext; simpa [lo] using congrArg Fin.val h
      · intro h; have := congrArg Fin.val h; rw [hrev] at this; have := i.2; simp at *; omega
    rw [hfix]
  rw [Finset.prod_congr rfl hrest]
  have hkn : k.val < n := by omega
  rw [dite_eq_left hkn, dite_eq_left hkn, hdiag, hact]
  beta_reduce
  rw [Function.update_self]
  have hlk : (⟨k.val, hkn⟩ : Fin n) = lo k := rfl
  rw [hlk, hs, Equiv.swap_apply_left, hord]
  have he : ((n : ℤ) - 1 - 2 * (k.val : ℤ)) = 1 := by
    have : (n : ℤ) = m + m := by exact_mod_cast hm
    have h2 : (k.val : ℤ) + 1 = m := by exact_mod_cast hkv
    omega
  rw [he]
  set r := ordL (T (lo k) (lo k))
  have hα : (α k : ℂ) ≠ 0 := (α k).ne_zero
  have hq1 : (q : ℂ) ^ (-(-r) * (1 : ℤ)) * (q : ℂ) ^ (-2 * r) = (q : ℂ) ^ (-r * (1 : ℤ)) := by
    rw [← zpow_add₀ hq]; congr 1; ring
  rw [Units.val_inv_eq_inv_val, inv_zpow', ← hq1]
  ring

end GKUnitary

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsLocEqOfIsLocComp
section
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CuspRep.ParLawsT

variable {E Ω : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}

theorem locParT_eq_of_isLocComp (hT : UpperTheory.Zero.LLC.RecTExists) {π : CuspSub E a} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) (h : IsPlaceOver A w) :
    locParT hT (CG.mk π) h = locRecT hT h (cls (ParLaws.toRep σ)) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [locParT, CG.IsLoc.unique E a _ w _ _ h1.loc h1]
  rfl

theorem cls_loc_eq_of_isLocComp {π : CuspSub E a} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) :
    (⟨a, ParLaws.toCl ((CG.mk π).loc w)⟩ : IrrGL (k := w.adicCompletion E)) = cls (ParLaws.toRep σ) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [CG.IsLoc.unique E a _ w _ _ h1.loc h1]
  rfl

theorem locParT_ofChar_eq (hT : UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) :
    locParT hT (CG.ofChar χ) h = locRecT hT h (.ofChar (χ.loc w) (ParLaws.isSmoothChar_loc χ w)) :=
  locParT_eq_of_isLocComp hT (CG.isLoc_ofChar χ w) h

end GlobalTheory.CuspRep.ParLawsT

theorem GlobalTheory.CuspRep.ParLawsT.locParT_twist : ∀ (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hT : UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (π : CG E a) (χ : HChar E) (h : IsPlaceOver A w), UpperTheory.Zero.LLC.Good (⟨a, ParLaws.toCl (π.loc w)⟩ : IrrGL (k := w.adicCompletion E)) → locParT hT (π.twist χ) h = (locParT hT π h).lpChar (locParT hT (CG.ofChar χ) h) := by
  intro hF hT E Ω _ _ _ _ _ _ A w a π χ h hg
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  obtain ⟨_, _, H⟩ := isRecT_locRecT hT h
  have hg' : UpperTheory.Zero.LLC.Good (cls (ParLaws.toRep σ)) := cls_loc_eq_of_isLocComp hσ ▸ hg
  refine (locParT_eq_of_isLocComp hT (hσ.twist χ) h).trans ?_
  rw [locParT_ofChar_eq, show locParT hT (Quotient.mk _ π) h = _ from locParT_eq_of_isLocComp hT hσ h, ← H.twist _ _ _ hg']
  exact congrArg _ (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjIdeleMapMaxRealSubfield
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ConjIdeleReal

theorem adeleMap_eq_baseChange (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L = GroundTheory.Global.AdeleBaseChange.adeleMap K L := by
  ext a : 1
  apply Prod.ext
  · funext w
    open scoped NumberField.LiesOver in
    change AbsoluteValue.Completion.map _ _ _ = algebraMap _ _ _
    rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver]
  · apply FiniteAdeleRing.ext
    intro w
    change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w _ =
      GroundTheory.Global.SemiLocal.completionMap _ w _
    rfl

theorem ideleConj_ideleMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b := by
  intro E _ _ _ b
  let alg : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  have tw : @IsScalarTower (maximalRealSubfield E) E E _ (@Algebra.toSMul _ _ _ _ alg) _ :=
    @IsScalarTower.of_algebraMap_eq (maximalRealSubfield E) E E _ _ _ _ alg _ fun x =>
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).commutes x).symm
  have h := @GroundTheory.Global.AdeleBaseChange.adeleMap_adeleMap (maximalRealSubfield E) E E _ _ _ _ _ _ _ alg _ tw
    (b : AdeleRing _ _)
  rw [← adeleMap_eq_baseChange, ← adeleMap_eq_baseChange] at h
  apply Units.ext
  exact h

end GlobalTheory.ConjIdeleReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjMemFiniteUnitIdeles
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjUnit

theorem ideleConj_mem_unitIdl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (y : Neutral.B1.Ideles E), y ∈ GlobalTheory.Mem.Chr.unitIdl E →
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y ∈ GlobalTheory.Mem.Chr.unitIdl E := by
  intro E _ _ _ y hy
  letI : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  have key : ∀ z : Neutral.B1.Ideles E, z ∈ GlobalTheory.Mem.Chr.unitIdl E → ∀ w : HeightOneSpectrum (𝓞 E),
      Valued.v (((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E z : AdeleRing (𝓞 E) E)).2 w) ≤ 1 := by
    intro z hz w
    have hz' : ∀ v : HeightOneSpectrum (𝓞 E), ((z : AdeleRing (𝓞 E) E)).2 v ∈ v.adicCompletionIntegers E :=
      fun v => (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := v)).mpr (hz v).le
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_mapsTo E E w (hz' _)
  intro w
  have h1 := key y hy w
  have h2 := key y⁻¹ (inv_mem hy) w
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y : AdeleRing (𝓞 E) E)).2 w *
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y⁻¹ : AdeleRing (𝓞 E) E)).2 w = 1 := by
    rw [map_inv]
    exact congrArg (fun a : AdeleRing (𝓞 E) E => a.2 w) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y).mul_inv
  have e' := congrArg Valued.v e
  rw [map_mul, map_one] at e'
  exact eq_one_of_one_le_mul_left h1 h2 e'.ge

end GlobalTheory.ConjUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjAverageUnipotentLocallyConstantCompactSupporStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjAverage_unipotent_locallyConstant_compactSupport : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m (x + y)) = GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m x)) ∧ HasCompactSupport (fun X => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m X)) := by
  first | exact @GlobalTheory.LeviDesc.UnipMean.cavg_blk_locConst_compactSupport | exact GlobalTheory.LeviDesc.UnipMean.cavg_blk_locConst_compactSupport | (intros; apply GlobalTheory.LeviDesc.UnipMean.cavg_blk_locConst_compactSupport <;> assumption)
end

