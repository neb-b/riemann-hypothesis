module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0203
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0219
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0037
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAnalyticSetupPeriodLatticePair

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementUnique
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorus

theorem idelicFrameTorusElement_apply_column_decomposition {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J} (ha : IsIdTorusElt σ J X Y l a) (z : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J a).1 *ᵥ z =
      adMat F X *ᵥ (diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) *ᵥ
          (adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z)) +
      adMat F Y *ᵥ (diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) *ᵥ
          (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z)) +
      (z - adMat F X *ᵥ (adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z)
         - adMat F Y *ᵥ (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z)) := by
  set P := adMat F (Formalism.UG.cT (σ : E →+* E) X * J)
  set Q := adMat F (Formalism.UG.cT (σ : E →+* E) Y * J)
  have mm : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E),
      adMat F A * adMat F B = adMat F (A * B) := fun A B => (Matrix.map_mul).symm
  have hPX : P * adMat F X = 0 := by rw [mm, hW.xx]; simp
  have hPY : P * adMat F Y = 1 := by rw [mm, hW.xy]; simp
  have hQX : Q * adMat F X = 1 := by rw [mm, yx h hJ hW]; simp
  have hQY : Q * adMat F Y = 0 := by rw [mm, hW.yy]; simp
  set w := z - adMat F X *ᵥ (Q *ᵥ z) - adMat F Y *ᵥ (P *ᵥ z) with hw
  have hPw : P *ᵥ w = 0 := by
    rw [hw, mulVec_sub, mulVec_sub, mulVec_mulVec (M := P) (N := adMat F X), mulVec_mulVec (M := P) (N := adMat F Y), hPX, hPY,
      zero_mulVec, one_mulVec]; simp
  have hQw : Q *ᵥ w = 0 := by
    rw [hw, mulVec_sub, mulVec_sub, mulVec_mulVec (M := Q) (N := adMat F X), mulVec_mulVec (M := Q) (N := adMat F Y), hQX, hQY,
      zero_mulVec, one_mulVec]; simp
  have hmem : w ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ := by
    refine ⟨(Submodule.mem_iInf _).2 fun i => (Submodule.mem_iInf _).2 fun _ => LinearMap.mem_ker.2 ?_,
      (Submodule.mem_iInf _).2 fun i => (Submodule.mem_iInf _).2 fun _ => LinearMap.mem_ker.2 ?_⟩
    · exact congrFun hPw i
    · exact congrFun hQw i
  have hz : z = adMat F X *ᵥ (Q *ᵥ z) + adMat F Y *ᵥ (P *ᵥ z) + w := by rw [hw]; abel
  conv_lhs => rw [hz]
  rw [mulVec_add, mulVec_add, mulVec_mulVec (N := adMat F X), mulVec_mulVec (N := adMat F Y), ha.1, ha.2.1,
    ha.2.2 w hmem, ← mulVec_mulVec, ← mulVec_mulVec]

theorem isIdTorusElt_uniq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a b : GAd σ J}, IsIdTorusElt σ J X Y l a → IsIdTorusElt σ J X Y l b → a = b := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW l a b ha hb
  apply matHom_injective (AF F) σ J
  apply Units.ext
  have hv : ∀ z, (matHom _ σ J a).1 *ᵥ z = (matHom _ σ J b).1 *ᵥ z := fun z => by
    rw [idelicFrameTorusElement_apply_column_decomposition h hJ hW ha, idelicFrameTorusElement_apply_column_decomposition h hJ hW hb]
  ext i j
  simpa [mulVec_single_one] using congrFun (hv (Pi.single j 1)) i

end GlobalTheory.IdTorus

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableOrbitalIntegralPreservedLatticeIsometry
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsomPhi

open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (gam centMeas orbCls torEmb)

theorem tor_mul_comm {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k] (a b : Tor P k) : a * b = b * a := by
  apply Subtype.ext
  show a.1 * b.1 = b.1 * a.1
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem map_isHaar_rightInv {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k] [TopologicalSpace k] {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [MeasurableSpace (Tor P k)] [BorelSpace (Tor P k)]
    [IsTopologicalGroup (Tor P k)] (e : Tor P k ≃ₜ* H) (dt : Measure (Tor P k)) [dt.IsHaarMeasure] :
    (dt.map e).IsHaarMeasure ∧ (dt.map e).IsMulRightInvariant := by
  haveI h1 : (dt.map e).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map dt e.toMulEquiv e.continuous e.symm.continuous
  refine ⟨h1, ⟨fun g => ?_⟩⟩
  have hc : (fun x : H => x * g) = fun x => g * x := funext fun x => by
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, tor_mul_comm]
  rw [hc]
  exact map_mul_left_eq_self _ g


set_option maxHeartbeats 4000000 in
open GlobalTheory.Orb in
theorem phi_map : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (P : PPol D.sp.cm.sig r) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v)) (dt : Measure (Tor P (Fv D.host.F v))) (f : GLoc D.sp.cm.sig V.gram v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → PhiOK (J := V.gram) μ dt f → PhiOK (J := V'.gram) (μ.map j) dt (f ∘ j.symm) → Phi (J := V'.gram) (μ.map j) dt (f ∘ j.symm) = Phi (J := V.gram) μ dt f := by
  intro D V V' r P v j hj μ dt f hμ hdt hok hok'
  have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  obtain ⟨hX, hmv⟩ := _root_.GlobalTheory.trEll_latticeConj_move _ _ D.sp.cm.sig hcm r V.rank V'.rank P V.gram V'.gram (frameLat V) (frameLat V')
    v j hj
  unfold Phi
  rw [← finsum_comp_equiv (Equiv.subtypeEquivRight (fun c => by rw [hX]))]
  refine finsum_congr fun q => ?_
  obtain ⟨c, h2⟩ := q
  obtain ⟨x, φ, hc, h⟩ := id h2
  subst hc
  obtain ⟨φ'', h'', hγ, ht⟩ := hmv x φ h
  obtain ⟨e, he, hme⟩ := _root_.GlobalTheory.TorCentTop.torEquiv_cent _ _ D.sp.cm.sig hcm r V.rank P V.gram (isHermND_gram V) (Fv D.host.F v) x φ h
  obtain ⟨e'', he'', hme''⟩ :=
    _root_.GlobalTheory.TorCentTop.torEquiv_cent _ _ D.sp.cm.sig hcm r V'.rank P V'.gram (isHermND_gram V') (Fv D.host.F v) x φ'' h''
  haveI := hμ
  haveI := hdt
  obtain ⟨i1, i2⟩ := map_isHaar_rightInv P (Fv D.host.F v) e dt
  haveI : (centMeas h dt).IsHaarMeasure := by rw [hme dt]; exact i1
  haveI : (centMeas h dt).IsMulRightInvariant := by rw [hme dt]; exact i2
  have v1 := (hok.2 x φ h).orbInt_eq
  have v2 := (hok'.2 x φ'' h'').orbInt_eq
  have hm : centMeas h'' dt = (centMeas h dt).map (centEquiv j (gam h) hγ.symm) := by
    rw [hme'', hme dt, Measure.map_map (map_continuous (centEquiv j (gam h) hγ.symm)).measurable (map_continuous e).measurable]
    congr 1
    funext t
    apply Subtype.ext
    rw [he'', ht, ← he]
    rfl
  calc orbCls (J := V'.gram) (μ.map j) dt (f ∘ j.symm) ((Equiv.subtypeEquivRight (fun c => by rw [hX])) ⟨QuotientGroup.mk x, h2⟩)
      = orbInt (μ.map j) (gam h'') (centMeas h'' dt) (f ∘ j.symm) := v2.symm
    _ = orbInt (μ.map j) (gam h'') ((centMeas h dt).map (centEquiv j (gam h) hγ.symm)) (f ∘ j.symm) := by rw [hm]
    _ = orbInt μ (gam h) (centMeas h dt) ((f ∘ j.symm) ∘ j) := (hasOrbInt_map j hγ.symm (f ∘ j.symm) 0).2
    _ = orbInt μ (gam h) (centMeas h dt) f := by
      congr 1
      ext g
      simp
    _ = orbCls (J := V.gram) μ dt f ⟨QuotientGroup.mk x, h2⟩ := v1

end GlobalTheory.IsomPhi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionDensitiesPartitionUnityEqZero
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem sum_corrDens_eq_zero : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), ∀ {ι : Type} [Fintype ι] (ρ : ι → CxPts X.str σ → ℝ), (∀ i y, CInfAt (ρ i) y) → (∀ y, ∑ i, ρ i y = 1) → ∀ (c : AlgChart X.str σ X.dim) (y : CxPts X.str σ), y ∈ c.e.source → ∑ i, corrDens E H₀ H (ρ i) c y = 0 := by
  intro F _ σ X m E O H H₀ ι _ ρ hρ h1 c y hy
  have hc : IsHoloChart c.e := c.holo
  have key := _root_.GlobalTheory.GoodTop.corrC_sum_eq_zero (fun i v => ρ i (c.e.symm v))
    (fun v => H₀ (E.nonempty (under y)).choose (c.e.symm v) ())
    (fun v => H (E.nonempty (under y)).choose (c.e.symm v) ()) (c.e y)
    (fun i => (contDiffAt_holoChart hc hy (hρ i y)).differentiableAt (by simp))
    (fun x => h1 _)
  simp only [corrDens, corrTop]
  rw [← Finset.mul_sum, ← Complex.re_sum, key]
  simp

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open GlobalTheory.VB GlobalTheory.Conormal
open GlobalTheory.KS.DerMorK (deformHom hom_ext_appLE)

namespace GlobalTheory.LieVB.TangentSurj

section General

variable {S X T : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (p : T ⟶ S) (ε : Γ(T, ⊤)) (hε : ε * ε = 0)
  (D : Der π e (structureModule S))

def val {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) : Γ(X, W) →+ Γ(S, V) := D.app h

theorem val_mul {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) (f g : Γ(X, W)) :
    val D h (f * g) = e.appLE W V h f * val D h g + e.appLE W V h g * val D h f :=
  D.app_mul h f g

theorem val_base {W : X.Opens} {V U : S.Opens} (h : V ≤ e ⁻¹ᵁ W) (k : W ≤ π ⁻¹ᵁ U) (a : Γ(S, U)) :
    val D h (π.appLE U W k a) = 0 := D.app_base h k a

theorem val_one {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) : val D h 1 = 0 := by
  simpa using val_base D (U := ⊤) h le_top 1

theorem val_res {W W' : X.Opens} (k : W' ≤ W) (f : Γ(X, W)) :
    val D (le_refl (e ⁻¹ᵁ W')) (resG X k f) = resG S (e.preimage_mono k) (val D le_rfl f) :=
  (D.app_res _ k f).trans (D.res_app le_rfl (e.preimage_mono k) f).symm


include hε in
theorem res_sq (U : T.Opens) : resG T (le_top : U ≤ ⊤) ε * resG T (le_top : U ≤ ⊤) ε = 0 := by
  rw [← map_mul, hε, map_zero]

def psi (W : X.Opens) : Γ(X, W) →+* Γ(T, p ⁻¹ᵁ e ⁻¹ᵁ W) where
  toFun f := p.appLE _ _ le_rfl (e.appLE W _ le_rfl f) +
    p.appLE _ _ le_rfl (val D le_rfl f) * resG T le_top ε
  map_one' := by simp only [val_one, map_one, map_zero, zero_mul, add_zero]
  map_mul' f g := by
    simp only [val_mul, map_mul, map_add (f := _)]
    linear_combination -(p.appLE _ _ le_rfl (val D le_rfl f) * p.appLE _ _ le_rfl (val D le_rfl g)) *
      res_sq ε hε (p ⁻¹ᵁ e ⁻¹ᵁ W)
  map_zero' := by simp only [map_zero, zero_mul, add_zero]
  map_add' f g := by
    simp only [map_add (f := _)]
    ring

theorem psi_apply (W : X.Opens) (f : Γ(X, W)) : psi p ε hε D W f =
    p.appLE _ _ le_rfl (e.appLE W _ le_rfl f) +
      p.appLE _ _ le_rfl (val D le_rfl f) * resG T le_top ε := rfl

theorem psi_nat (W W' : X.Opens) (h : W' ≤ W) (f : Γ(X, W)) :
    psi p ε hε D W' (resG X h f) =
      resG T (p.preimage_mono (e.preimage_mono h)) (psi p ε hε D W f) := by
  rw [psi_apply, psi_apply, val_res, map_add (f := _), map_mul, resG_resG, resG_appLE, resG_appLE,
    appLE_resG e, appLE_resG p, ← resG_appLE e (e.preimage_mono h) le_rfl, appLE_resG p]

theorem psi_nil (W : X.Opens) (f : Γ(X, W)) :
    IsNilpotent (psi p ε hε D W f - p.appLE _ _ le_rfl (e.appLE W _ le_rfl f)) := by
  refine ⟨2, ?_⟩
  rw [psi_apply]
  linear_combination (p.appLE _ _ le_rfl (val D le_rfl f)) ^ 2 * res_sq ε hε (p ⁻¹ᵁ e ⁻¹ᵁ W)

def deform : T ⟶ X :=
  deformHom (p ≫ e) (psi p ε hε D) (psi_nat p ε hε D) fun W f => by
    have h : ((p ≫ e).app W).hom f = p.appLE _ _ le_rfl (e.appLE W _ le_rfl f) := by
      rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app]; rfl
    rw [h]
    exact psi_nil p ε hε D W f

theorem deform_appLE (W : X.Opens) {U : T.Opens} (k : U ≤ p ⁻¹ᵁ e ⁻¹ᵁ W) (f : Γ(X, W)) :
    (deform p ε hε D).appLE W U k f = resG T k (psi p ε hε D W f) := rfl

theorem deform_comp (he : e ≫ π = 𝟙 S) : deform p ε hε D ≫ π = p := by
  have h₀ : p ≫ e ≫ π = p := by rw [he, Category.comp_id]
  refine hom_ext_appLE (congr(($h₀).base)) fun U k => ?_
  ext a
  have k' : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ e ⁻¹ᵁ π ⁻¹ᵁ U := k
  refine (appLE_appLE (f := deform p ε hε D) rfl le_rfl k' k a).symm.trans ?_
  rw [deform_appLE, psi_apply, val_base, map_zero, zero_mul, add_zero,
    appLE_base he _ _ ((le_preimage_iff he).1 le_rfl), appLE_resG, resG_appLE,
    Scheme.Hom.appLE_eq_app]

theorem comp_deform {z : S ⟶ T} (hz : z ≫ p = 𝟙 S) (h0 : z.appLE ⊤ ⊤ le_top ε = 0) :
    z ≫ deform p ε hε D = e := by
  have h₀ : z ≫ p ≫ e = e := by rw [reassoc_of% hz]
  refine hom_ext_appLE (congr(($h₀).base)) fun W k => ?_
  ext f
  have k' : e ⁻¹ᵁ W ≤ z ⁻¹ᵁ p ⁻¹ᵁ e ⁻¹ᵁ W := k
  refine (appLE_appLE (f := z) (g := deform p ε hε D) (V := p ⁻¹ᵁ e ⁻¹ᵁ W)
    rfl le_rfl k' k f).symm.trans ?_
  rw [deform_appLE, resG_self, psi_apply, map_add (f := _), map_mul, appLE_resG,
    ← resG_appLE z le_top le_top ε, h0, map_zero, mul_zero, add_zero,
    appLE_base hz _ _ le_rfl, resG_self, Scheme.Hom.appLE_eq_app]

end General

variable (O : Type) [CommRing O]

theorem epsFn_sq : epsFn O * epsFn O = 0 := by
  have h := map_mul (Scheme.ΓSpecIso (.of (DualNumber O))).inv.hom DualNumber.eps DualNumber.eps
  rw [DualNumber.eps_mul_eps, map_zero] at h
  exact h.symm

theorem epsZero_epsFn : (sec (epsZero O)).appLE ⊤ ⊤ le_top (epsFn O) = 0 := by
  refine congr($(Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom O O O).toRingHom)) DualNumber.eps).symm.trans ?_
  exact (congrArg (Scheme.ΓSpecIso (.of O)).inv.hom (DualNumber.fst_eps (R := O))).trans
    (map_zero _)

theorem tangent_surjective (O : Type) [CommRing O] (G : Over (Sp O)) [GrpObj G] :
    Function.Surjective (tangent : LieG G → Γ(Lie G, ⊤)) := by
  intro l
  let D := lieEquivDer G l
  let x : specO O (DualNumber O) ⟶ G :=
    Over.homMk (deform (specO O (DualNumber O)).hom (epsFn O) (epsFn_sq O) D)
      (deform_comp _ _ _ D (sec_hom η[G]))
  have hx : ptMap (TrivSqZeroExt.fstHom O O O) ≫ x = toUnit (specO O O) ≫ η[G] := by
    have h : (toUnit (specO O O)).left = 𝟙 (Sp O) := by
      rw [Over.toUnit_left]
      exact Spec.map_id _
    ext1
    simp only [Over.comp_left, h]
    exact (comp_deform _ _ (epsFn_sq O) D (sec_hom (epsZero O)) (epsZero_epsFn O)).trans
      (Category.id_comp _).symm
  refine ⟨⟨x, hx⟩, (homGlobalEquiv _ _).injective (omega_hom_ext fun W f => ?_)⟩
  refine dualApp_tangent_dUnit ⟨x, hx⟩ le_rfl f
    ((le_preimage_iff (sec_hom (epsZero O))).2 le_rfl) le_rfl le_rfl
    ((unitSec G).appLE W _ le_rfl f) (val D le_rfl f) ?_
  exact (deform_appLE _ _ (epsFn_sq O) D W le_rfl f).trans (resG_self _ _)

end GlobalTheory.LieVB.TangentSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionO1ProjectiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_self_intersection_O1_projective : ∀ (k : Type) [Field k] (N : ℕ), letI := GlobalTheory.algebraΓOfHom (PSpace.str k N); topSelfIntersection k (ProjSpace.O1 k N) N = 1 := by
  first | exact @GlobalTheory.ProjSpaceDegree.topSelf_O1_str | exact GlobalTheory.ProjSpaceDegree.topSelf_O1_str | (intros; apply GlobalTheory.ProjSpaceDegree.topSelf_O1_str <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimGen
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB

namespace GlobalTheory.Vert.Model

theorem topologicalKrullDim_gen : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z : Model O), topologicalKrullDim Z.gen.toScheme = Z.relDim := by
  intro O _ _ _ Z
  obtain ⟨q, H⟩ := Z.exists_isPullback_gen (FractionRing O)
  obtain ⟨d, hd, -⟩ := exists_topologicalKrullDim_fibres_eq_of_isPullback Z.str (FractionRing O)
    (IsLocalRing.ResidueField O) IsLocalRing.residue_surjective (IsPullback.of_hasPullback _ _) H
  rw [hd, relDim_eq_iff.2
    (IntModel.topologicalKrullDim_eq_succ (IsDiscreteValuationRing.not_isField O) H hd)]

end GlobalTheory.Vert.Model
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLatticeStandardPointsScaledEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LaStdEntries

open Formalism.MainNotions.TaylorLogMetric Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7}

def entSub (D : D7) (a b : ℕ) (S : Submodule (𝓞 D.host.E) D.host.E) :
    Submodule (𝓞 D.host.E) (Matrix (Fin b) (Fin a) D.host.E) where
  carrier := {A | ∀ i j, A i j ∈ S}
  add_mem' hA hB i j := by simpa using S.add_mem (hA i j) (hB i j)
  zero_mem' i j := by simp
  smul_mem' o A hA i j := by simpa using S.smul_mem o (hA i j)

theorem homL_le {a b : ℕ} :
    homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D b) ≤ entSub D a b 1 := by
  refine Submodule.span_le.mpr ?_
  intro A hA i j
  have hj : (Pi.single j (1 : D.host.E) : Fin a → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D a := by
    simp only [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_implies]
    intro k
    by_cases hk : k = j
    · subst hk; simp [Submodule.one_eq_range]
    · simp [Pi.single_apply, hk]
  have h := hA _ hj
  simp only [Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at h
  have := h i
  simpa [Matrix.mulVec_single] using this

theorem YYl_le {a b : ℕ} :
    YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D b)
      ≤ entSub D a b (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  refine Submodule.span_le.mpr ?_
  rintro B ⟨x, hx, A, hA, rfl⟩ i j
  obtain ⟨o, ho⟩ := (Submodule.mem_one).1 (homL_le hA i j)
  show x * A i j ∈ _
  rw [← ho, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ o hx

theorem K_mul_mem_AA {c : 𝓞 D.host.K} (hc : c ∈ D.host.ccK) {x : D.host.E}
    (hx : x ∈ D.host.AA0) : ((c : D.host.K) : D.host.E) * x ∈ D.host.AA := by
  show _ ∈ (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0
  refine FractionalIdeal.mul_mem_mul ?_ hx
  rw [FractionalIdeal.mem_coeIdeal]
  exact ⟨_, Ideal.mem_map_of_mem _ hc, rfl⟩

theorem La_std_rep : ∀ {D : D7} (δ : ℂ) {a b : ℕ} (x : Formalism.MainNotions.TaylorLogMetric.VC D a b),
    x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D b) →
    ∃ M : Matrix (Fin b) (Fin a) D.host.E, (∀ i j, M i j ∈ D.host.AA) ∧
      x = δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M := by
  intro D δ a b x hx
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    obtain ⟨c, hc, rfl⟩ := FL.lam_mem D D.host.ccK δ w hw
    refine ⟨((c : D.host.K) : D.host.E) • A, fun i j => ?_, ?_⟩
    · simpa using K_mul_mem_AA hc (YYl_le hA i j)
    · rw [GlobalTheory.MomSetup.embV_smulK, smul_smul]
  | zero => exact ⟨0, fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).zero_mem, by rw [GlobalTheory.MomSetup.embV_zero, smul_zero]⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨A, hA, rfl⟩ := h1
    obtain ⟨B, hB, rfl⟩ := h2
    exact ⟨A + B, fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).add_mem (hA i j) (hB i j),
      by rw [GlobalTheory.MomSetup.embV_add, smul_add]⟩
  | neg x _ h =>
    obtain ⟨A, hA, rfl⟩ := h
    exact ⟨-A, fun i j => (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).neg_mem (hA i j), by rw [GlobalTheory.MomSetup.embV_neg, smul_neg]⟩

end GlobalTheory.LaStdEntries
end
end

