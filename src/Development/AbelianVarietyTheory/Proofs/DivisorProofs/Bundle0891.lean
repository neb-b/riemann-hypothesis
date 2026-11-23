module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ProjectiveOfIsLocallyConstantFinrankFiber
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0848

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveTriLat
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotMove

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7} {T : Type} {A A' WW : HSp D}

def moveTri (Y : Tri T A A' WW) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
    (g : GA D A) (g' : GA D A') (h : GA D WW) (t₀ : T) (r r' : T → ℂ) : Tri T A A' WW where
  rA := ⟨ΛA, Lev.finE A g * Y.rA.β, Y.rA.s, Y.rA.B⟩
  rA' := ⟨ΛA', Lev.finE A' g' * Y.rA'.β, Y.rA'.s, Y.rA'.B⟩
  rW := ⟨ΛW, Lev.finE WW h * Y.rW.β, Y.rW.s, Y.rW.B⟩
  ω := Y.ω
  ω' := Y.ω'
  vac := Y.ω t₀ (g, h) Y.vac
  vac' := Y.ω' t₀ (g', h) Y.vac'
  e := Y.e
  c := Y.c
  f t := (r t)⁻¹ • Y.ω t (g, h) (Y.f t)
  f' t := (r' t)⁻¹ • Y.ω' t (g', h) (Y.f' t)
  m := Y.m.map (fun x => x * g⁻¹)
  fd := (fun x => x * g) ⁻¹' Y.fd
  m' := Y.m'.map (fun x => x * g'⁻¹)
  fd' := (fun x => x * g') ⁻¹' Y.fd'

variable (Y : Tri T A A' WW) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
  (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
  (g : GA D A) (g' : GA D A') (h : GA D WW) (t₀ : T) (r r' : T → ℂ)

end GlobalTheory.BotMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulFunEqOneOfEqOneOnMaxCompact
section
namespace GlobalTheory.FrameEquiv

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem mulFun_eq_one_of_eq_one_on_maxCompact : ∀ (D : D7) (T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ τ, IsCartanInv (gramAt D T τ) (s τ)) → ∀ χ : GA D T → ℂ, (∀ u ∈ GinfC T, ∀ u' ∈ GinfC T, χ (u * u') = χ u * χ u') → (∀ k ∈ GinfC T, (∀ τ, compAt θ τ (Formalism.L2.Theta.mt T k) * s τ = s τ * compAt θ τ (Formalism.L2.Theta.mt T k)) → χ k = 1) → ∀ u ∈ GinfC T, χ u = 1 :=
  fun D T θ hθ s hs χ hm hK =>
    GlobalTheory.UnitaryChar.char_eq_one D θ T hθ s hs χ hm fun k hk h => hK k hk fun τ => (h τ).symm

end GlobalTheory.FrameEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaOperatorFrameSeriesOfSteps
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

section NabAux

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}


open Classical in
def colCoef {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ)
    (lam : Let cx) (ℓ : LtN Dw n) : k :=
  ∑ j : Fin n, if ℓ = ⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2, j⟩ then B lam.1.1.1 lam.1.2 j else 0

theorem sum_colCoef_smul {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ)
    (lam : Let cx) {M : Type} [AddCommGroup M] [Module k M] (x : LtN Dw n → M) :
    ∑ ℓ, colCoef B cx lam ℓ • x ℓ =
      ∑ j : Fin n, B lam.1.1.1 lam.1.2 j • x ⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2, j⟩ := by
  classical
  simp only [colCoef, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2, j⟩ : LtN Dw n)]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem polyP_eq_aeval {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) :
    polyP B cx = MvPolynomial.aeval (fun lam : Let cx => ∑ ℓ, MvPolynomial.C (colCoef B cx lam ℓ) *
      (MvPolynomial.X ℓ : MvPolynomial (LtN Dw n) k)) (polyH k cx) := by
  classical
  unfold polyP polyH
  rw [map_prod, ← Finset.prod_filter_of_ne (p := fun f => cx f ≠ 0)
    (fun f _ hf h0 => hf (by rw [h0, pow_zero])),
    Finset.prod_subtype (p := fun f => cx f ≠ 0) (F := inferInstance) _ (by simp)]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [MvPolynomial.aeval_rename, detPow, map_pow, AlgHom.map_det, ← Matrix.det_transpose]
  congr 2
  ext1 a b
  simp only [GlobalTheory.CombMinor.cMat, Matrix.transpose_apply, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply,
    MvPolynomial.aeval_X, Function.comp_apply, MvPolynomial.C_mul']
  rw [sum_colCoef_smul]

theorem map_polyP {k k' : Type} [Field k] [Field k'] (φ : k →+* k') {n : ℕ}
    (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) :
    MvPolynomial.map φ (polyP B cx) = polyP (fun f b j => φ (B f b j)) cx := by
  unfold polyP
  rw [map_prod]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext1 a b
  simp [GlobalTheory.CombMinor.cMat]

theorem subst_colCoef_expPt {k : Type} [Field k] {v : AddValuation k (WithTop ℝ)} {d n : ℕ} (G : LogFGL v d)
    (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) (u : Lt1 Dw → Fin d → k) (Φ : PS k n d) :
    subst (fun ℓ : LtN Dw n => ∑ lam : Let cx, colCoef B cx lam ℓ • (X lam : MvPowerSeries (Let cx) k))
      (subst (fun q : Fin n × Fin d => expPt G (fun e => ∑ ℓ : LtN Dw n,
        (if ℓ.2.2 = q.1 then u ⟨ℓ.1, ℓ.2.1⟩ e else 0) • (X ℓ : MvPowerSeries (LtN Dw n) k)) q.2) Φ) =
    subst (fun q : Fin n × Fin d => expPt G (fun e => ∑ lam : Let cx,
      (B lam.1.1.1 lam.1.2 q.1 * u ⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2⟩ e) •
        (X lam : MvPowerSeries (Let cx) k)) q.2) Φ := by
  have ht : HasSubst (fun ℓ : LtN Dw n => ∑ lam : Let cx, colCoef B cx lam ℓ •
      (X lam : MvPowerSeries (Let cx) k)) := hasSubst_of_constantCoeff_zero (by simp)
  have hw : ∀ (j : Fin n) (e : Fin d), constantCoeff (∑ ℓ : LtN Dw n,
      (if ℓ.2.2 = j then u ⟨ℓ.1, ℓ.2.1⟩ e else 0) • (X ℓ : MvPowerSeries (LtN Dw n) k)) = 0 := by
    intro j e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun ℓ _ => by rw [constantCoeff_smul, constantCoeff_X, smul_zero]
  have hs : HasSubst (fun q : Fin n × Fin d => expPt G (fun e => ∑ ℓ : LtN Dw n,
      (if ℓ.2.2 = q.1 then u ⟨ℓ.1, ℓ.2.1⟩ e else 0) • (X ℓ : MvPowerSeries (LtN Dw n) k)) q.2) :=
    hasSubst_of_constantCoeff_zero fun q => cc_expPt G (hw q.1) q.2
  refine (subst_comp_subst_apply hs ht Φ).trans (congrArg (fun s => subst s Φ) (funext fun q => ?_))
  refine (subst_expPt G ht (hw q.1) q.2).trans (congrArg (fun s => expPt G s q.2) (funext fun e => ?_))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← coe_substAlgHom ht, map_sum, map_smul]
  simp only [coe_substAlgHom, subst_X ht, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have h := sum_colCoef_smul B cx lam
    (fun ℓ : LtN Dw n => if ℓ.2.2 = q.1 then u ⟨ℓ.1, ℓ.2.1⟩ e else 0)
  simp only [smul_eq_mul] at h
  rw [Finset.sum_congr rfl fun ℓ _ => mul_comm _ _, h]
  simp

end NabAux

theorem nabSt_of : InvDerSt → LinSt → FrameSt → NabSt := by
  intro hI hL hF E _ _ _ H Dw l Xo c _ T io y Ch p _ X cx n B k g
  let _ := io.toAlgebra
  let _ : Algebra T.Fr X.C := X.ιF.toAlgebra
  have hfr := (hF X.C (vX_vp X) (chD Ch.ch) T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch X) _ (gauge_chart Ch X) H.w0 n).2.1 k
  have hinv := hI X.C (vX_vp X) (chD Ch.ch) (lawX Ch X) (fgl Ch X).F_int n (LtN Dw n) (fun ℓ => ℓ.2.2)
    (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map X.ιF (polyT B cx)) (g * frameX Ch X n ^ k)
  have hP : MvPolynomial.map X.ιF (polyT B cx) = polyP (fun f b j => jX X (B f b j)) cx := map_polyP _ _ _
  unfold nabX nabValN
  rw [hfr]
  refine Eq.trans hinv ?_
  rw [hP, polyP_eq_aeval, hL]
  exact congrArg (derivAt0 (polyH X.C cx))
    (subst_colCoef_expPt (fgl Ch X) (fun f b j => jX X (B f b j)) cx (lieVec Ch X) (g * frameX Ch X n ^ k))

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegDefOfHermitianMatrixPositiveIndexEqZero
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem herm_negDef_of_sigPosH_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    A.det ≠ 0 → sigPosH hA = 0 → ∀ y : Fin n → ℂ, y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  intro hdet hsig y hy
  have hneg : ∀ i, hA.eigenvalues i < 0 := by
    intro i
    have hnp : ¬ 0 < hA.eigenvalues i := by
      intro h
      have : IsEmpty {i : Fin n // 0 < hA.eigenvalues i} := Fintype.card_eq_zero_iff.mp hsig
      exact this.false ⟨i, h⟩
    have hne : hA.eigenvalues i ≠ 0 := by
      intro h0
      apply hdet
      rw [hA.det_eq_prod_eigenvalues]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])
    exact lt_of_le_of_ne (not_lt.mp hnp) hne
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  set z : Fin n → ℂ := star U *ᵥ y with hz
  have hyz : y = U *ᵥ z := by rw [hz, mulVec_mulVec, hUU', one_mulVec]
  have hz0 : z ≠ 0 := by
    intro h; apply hy; rw [hyz, h, mulVec_zero]
  have hspec : A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
  have key : star y ⬝ᵥ A *ᵥ y = star z ⬝ᵥ diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ z := by
    conv_lhs => rw [hspec]
    rw [hz, star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, dotProduct_mulVec, vecMul_vecMul]
  rw [key]
  simp only [dotProduct, mulVec_diagonal, Function.comp_apply, Complex.re_sum]
  have hterm : ∀ i, (star z i * ((RCLike.ofReal (hA.eigenvalues i) : ℂ) * z i)).re =
      hA.eigenvalues i * Complex.normSq (z i) := by
    intro i
    rw [show (RCLike.ofReal (hA.eigenvalues i) : ℂ) = (hA.eigenvalues i : ℂ) from rfl,Pi.star_apply, mul_left_comm, Complex.re_ofReal_mul]
    congr 1
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  simp_rw [hterm]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz0
  rw [← Finset.sum_const_zero (s := (Finset.univ : Finset (Fin n)))]
  refine Finset.sum_lt_sum (fun i _ => mul_nonpos_of_nonpos_of_nonneg (hneg i).le (Complex.normSq_nonneg _))
    ⟨j, Finset.mem_univ j, mul_neg_of_neg_of_pos (hneg j) (Complex.normSq_pos.mpr hj)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.Adelic GlobalTheory.CechPic

namespace GlobalTheory.FieldChangeInter

variable {X X' : Scheme.{0}}

def cechIso {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X) {κ : Type} [LinearOrder κ]
    (D : κ → X.Opens) :
    letI := algebraΓOfHom f
    cechLB f M D ≅ cech R (LB.toMod M) ⊤ D :=
  letI := algebraΓOfHom f
  (cechFunctor κ R).mapIso (Cube.isoMk (fun s => LinearEquiv.ofBijective
    (M := SecOnR f M (⨅ i ∈ s, D i)) (M₂ := sectionsOn (LB.toMod M) (⊤ ⊓ ⨅ i ∈ s, D i))
    (SecOnR.restrict f M (inf_le_right : ⊤ ⊓ (⨅ i ∈ s, D i) ≤ ⨅ i ∈ s, D i))
    (SecOnR.restrict_bijective f _ (le_inf le_top le_rfl)))
    fun {s t} h x => (SecOnR.restrict_restrict f _ inf_le_right x).trans
      (SecOnR.restrict_restrict f inf_le_right (cechOpen_anti ⊤ D h) x).symm)

theorem nonempty_homology_equiv {R : Type} (O : Type) [CommRing R] [CommRing O]
    [Algebra R O] [Module.Flat R O] (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Nonempty ((((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).mapHomologicalComplex _).obj
      C).homology n ≃ₗ[O] O ⊗[R] C.homology n) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.2 (inferInstance : Module.Flat R O))
  have : (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R O)).isLeftAdjoint
  obtain ⟨e⟩ := Semicont.nonempty_extendScalars_obj_equiv O (C.homology n)
  exact ⟨((C.sc n).mapHomologyIso
    (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O))).toLinearEquiv ≪≫ₗ e⟩

theorem nonempty_coh_equiv {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {M : LB X} (hM : M.IsLB)
    {κ : Type} [LinearOrder κ] [Finite κ] {D : κ → X.Opens} (hc : ⨆ i, D i = ⊤)
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)) (n : ℕ) :
    letI := algebraΓOfHom f
    Nonempty ((cechLB f M D).homology n ≃ₗ[R] coh (twist (structureModule X) M) n) := by
  letI := algebraΓOfHom f
  haveI := LB.isQuasicoherent_toMod hM
  exact ⟨((HomologicalComplex.homologyFunctor _ _ n).mapIso (cechIso f M D)).toLinearEquiv ≪≫ₗ
    cechHEquivCoh R hc hD (LB.toMod M) n ≪≫ₗ (cohOn.mapIso R ⊤ n (Twist.unitTwistIso M)).symm⟩

variable {k E : Type} [Field k] [Field E] [Algebra k E] {f : X ⟶ Spec (CommRingCat.of k)}
  {f' : X' ⟶ Spec (CommRingCat.of E)} {π : X' ⟶ X}

theorem hdim_pull [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {M : LB X} (hM : M.IsLB) (n : ℕ) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom f'
    hdim E (twist (structureModule X') (M.pull π)) n = hdim k (twist (structureModule X) M) n := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  obtain ⟨e₁⟩ := nonempty_coh_equiv f hM hc hD' n
  obtain ⟨e₂⟩ := nonempty_coh_equiv f' (LB.isLB_pull hM π) (D := fun i => π ⁻¹ᵁ D i)
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) (fun s hs => isAffineOpen_biInf_preimage H (hD' s hs)) n
  obtain ⟨e₃⟩ := nonempty_homology_equiv E (cechLB f M D) n
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso (cechLBBaseChangeIso hM H hD')).toLinearEquiv
  rw [hdim_def, hdim_def, ← e₁.finrank_eq, ← e₂.finrank_eq]
  exact e₄.finrank_eq.symm.trans (e₃.finrank_eq.trans Module.finrank_baseChange)

theorem interNum_pull [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {ι : Type} [Fintype ι] {L : ι → LB X}
    (hL : ∀ i, (L i).IsLB) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom f'
    interNum E (structureModule X') (fun i => (L i).pull π) = interNum k (structureModule X) L := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have h : chiPic k (structureModule X) = chiPic E (structureModule X') ∘ pull π := by
    funext c
    obtain ⟨M, hM, rfl⟩ := cls_surj c
    exact finsum_congr fun n => congrArg (fun a : ℕ => (-1 : ℤ) ^ n * a) (hdim_pull H hM n).symm
  rw [interNum_eq_multiDiff k _ hL, h, multiDiff_comap, Function.comp_apply, map_zero,
    interNum_eq_multiDiff E _ fun i ↦ pull_isLB (hL i) π]
  rfl

theorem del_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (S : LinSys k),
    IsProjOver S.str → (S.baseChange E).del = S.del := by
  intro k E _ _ _ S h
  have : IsProper S.str := by
    obtain ⟨N, i, hi, e⟩ := h
    have := isProper_str k N
    rw [← e]
    infer_instance
  exact interNum_pull (ι := Fin S.D) (L := fun _ => S.L) (S.isPullback_baseChange E) fun _ => S.isLB

end GlobalTheory.FieldChangeInter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic

namespace GlobalTheory.Adelic.HeightScaling

variable {F K : Type} [Field F] [Field K] [NumberField K] {N n : ℕ}

theorem finite_support_log {c : K} (hc : c ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (v c)).Finite := by
  refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport hc) fun v hv h1 => hv ?_
  simp only at h1
  simp [h1]

theorem sum_log_eq_zero {c : K} (hc : c ≠ 0) :
    (∑ᶠ v : FinitePlace K, Real.log (v c)) + ∑ τ : K →+* ℂ, Real.log ‖τ c‖ = 0 := by
  have hmul : (Function.mulSupport fun w : FinitePlace K => w c).Finite :=
    FinitePlace.hasFiniteMulSupport hc
  have h1 : ∑ᶠ w : FinitePlace K, Real.log (w c) = Real.log (∏ᶠ w : FinitePlace K, w c) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hc).ne')]
    intro w hw
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    simp [h1]
  have h2 : ∑ φ : K →+* ℂ, Real.log ‖φ c‖ = Real.log |Algebra.norm ℚ c| := by
    rw [← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hc))]
    congr 1
    have := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ c)
    rw [norm_prod] at this
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ c‖) (fun φ => ‖φ c‖)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]
    rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hc]
  push_cast
  rw [Real.log_inv, neg_add_cancel]

theorem finite_support_log_finSize {w : Matrix (Fin N) (Fin n) F} (hw : Submodule.span F (Set.range w.col) = ⊤)
    (φ : F →+* K) {y : Fin N → K} (hy : y ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (finSize w φ v.1 y)).Finite := by
  have hfin : (⋃ k : {k : Fin n // ∑ j, φ (w j k) * y j ≠ 0},
      Function.mulSupport fun v : FinitePlace K => v (∑ j, φ (w j k.1) * y j)).Finite :=
    Set.finite_iUnion fun k => FinitePlace.hasFiniteMulSupport k.2
  refine hfin.subset fun v hv => ?_
  by_contra hn
  apply hv
  have h1 : ∀ k : Fin n, ∑ j, φ (w j k) * y j ≠ 0 → v.1 (∑ j, φ (w j k) * y j) = 1 := fun k hk => by
    by_contra h
    exact hn (Set.mem_iUnion.2 ⟨⟨k, hk⟩, h⟩)
  have hpos := finSize_pos hw φ v.1 hy
  have hle : finSize w φ v.1 y ≤ 1 := Real.iSup_le (fun k => by
    by_cases hk : ∑ j, φ (w j k) * y j = 0
    · rw [hk, map_zero]; exact zero_le_one
    · exact (h1 k hk).le) zero_le_one
  have hge : 1 ≤ finSize w φ v.1 y := by
    by_contra h
    refine hpos.not_ge (Real.iSup_le (fun k => ?_) le_rfl)
    by_cases hk : ∑ j, φ (w j k) * y j = 0
    · rw [hk, map_zero]
    · exact absurd ((h1 k hk).ge.trans (le_finSize w φ v.1 y k)) h
  simp only [le_antisymm hle hge, Real.log_one]

theorem pointHeight_smul : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (y : Fin N → K) (c : K), y ≠ 0 → c ≠ 0 → pointHeight w A (c • y) = pointHeight w A y := by
  intro F K _ _ _ _ _ N n w A hw hA y c hy hc
  rw [pointHeight_eq, pointHeight_eq]
  congr 1
  have e1 : ∀ v : FinitePlace K, Real.log (finSize w (algebraMap F K) v.1 (c • y)) =
      Real.log (v c) + Real.log (finSize w (algebraMap F K) v.1 y) := fun v => by
    rw [finSize_smul, Real.log_mul (v.1.ne_zero hc) (finSize_pos hw _ v.1 hy).ne']
    rfl
  have e2 : ∀ τ : K →+* ℂ, Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ ((c • y) j)) =
      Real.log ‖τ c‖ + Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ (y j)) := fun τ => by
    have h0 : (fun j => τ (y j)) ≠ 0 := fun h => hy (funext fun j => (map_eq_zero τ).1 (congrFun h j))
    have h1 : (fun j => τ ((c • y) j)) = τ c • fun j => τ (y j) := funext fun j => by simp
    rw [h1, archSize_smul, Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero τ).2 hc)) (archSize_pos (hA _) h0).ne']
  rw [finsum_congr e1, Finset.sum_congr rfl fun τ _ => e2 τ, Finset.sum_add_distrib,
    finsum_add_distrib (finite_support_log hc) (finite_support_log_finSize hw _ hy)]
  linarith [sum_log_eq_zero hc]

end GlobalTheory.Adelic.HeightScaling
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicTensorUnramifiedFrobTwistIterateDegree
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKRes

theorem tensorMap_id_iterate_eq_self {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : B →ₐ[R] B) (r : ℕ) (hf : ∀ b, (⇑f)^[r] b = b) (x : A ⊗[R] B) :
    (⇑(Algebra.TensorProduct.map (AlgHom.id R A) f))^[r] x = x := by
  set e := Algebra.TensorProduct.map (AlgHom.id R A) f
  have ht : ∀ k (a : A) (b : B), (⇑e)^[k] (a ⊗ₜ[R] b) = a ⊗ₜ[R] (⇑f)^[k] b := by
    intro k a b
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      simp [e]
  have hadd : ∀ k (x y : A ⊗[R] B), (⇑e)^[k] (x + y) = (⇑e)^[k] x + (⇑e)^[k] y := by
    intro k x y
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_add (f := _), Function.iterate_succ_apply',
        Function.iterate_succ_apply']
  have hzero : ∀ k, (⇑e)^[k] (0 : A ⊗[R] B) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_zero]
  induction x using TensorProduct.induction_on with
  | zero => exact hzero r
  | tmul a b => rw [ht, hf]
  | add x y hx hy => rw [hadd, hx, hy]

theorem sigKQ_iterate_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ),
    0 < r → ∀ x : KQ p K r, (⇑(sigKQ p K r))^[r] x = x := by
  intro p _ K r hr x
  exact tensorMap_id_iterate_eq_self (A := K) (frobQ p r) r (frobQ_iterate_self p r hr) x

end GlobalTheory.LKRes
end

