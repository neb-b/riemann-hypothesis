module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0781
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypeResidueCharsUnramifiedTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ExportSeries.TupleChars

variable {D : D7}

open GlobalTheory.StepLaw (ResAt UnrOff)

theorem idemSum_mul_idemAt {P Q : Finset (Pl D.host.E)} (h : SplitSet P) (hQ : Q ⊆ P) {PP : Pl D.host.E}
    (hPP : PP ∈ P) (hn : PP ∉ Q) : (idem Q + cA D (idem Q)) * idemAt PP = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [idem, map_sum, add_mul, Finset.sum_mul, Finset.sum_mul,
    Finset.sum_eq_zero fun i hi => h.mul_eq_zero (hQ hi) hPP (by rintro rfl; exact hn hi),
    Finset.sum_eq_zero fun i hi => by rw [mul_comm]; exact h.mul_conj hPP (hQ hi), add_zero]

theorem idemSum_mul_of_off {P Q : Finset (Pl D.host.E)} (h : SplitSet P) (hQ : Q ⊆ P) {PP : Pl D.host.E}
    (hPP : PP ∈ P) (hn : PP ∉ Q) {e : AE D} (he : IsIdemAt e PP) {x : AE D} (hx : e * (x - 1) = x - 1) :
    (idem Q + cA D (idem Q)) * x = idem Q + cA D (idem Q) := by
  have k := idemSum_mul_idemAt h hQ hPP hn
  rw [idemAt_eq he] at k
  linear_combination (-(idem Q + cA D (idem Q))) * hx + (x - 1) * k

theorem resAt_of_isResAt {χ : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {c : (kP PP)ˣ →* Circle} (h : IsResAt χ PP c) :
    ResAt χ PP (Circle.toUnits.comp c) := by
  intro e he x hx hi u hu
  have he' := idemAt_eq he
  rw [h x (by rw [he']; linear_combination (-1 : AE D) * hx) hi u hu.symm]
  rfl

theorem resAt_of_unram {χ : (AE D)ˣ →* Circle} {P Q : Finset (Pl D.host.E)} (hχ : UnramOutside χ Q) (h : SplitSet P)
    (hQ : Q ⊆ P) {PP : Pl D.host.E} (hPP : PP ∈ P) (hn : PP ∉ Q) : ResAt χ PP 1 := by
  intro e he x hx hi u hu
  have he' := idemAt_eq he
  have hfu := SpecGood.finUnit_of_res PP (by rw [he']; exact he) x
    (by rw [he']; linear_combination (-1 : AE D) * hx) hi u hu.symm
  rw [hχ x hfu.1 hfu.2.1 hfu.2.2 (idemSum_mul_of_off h hQ hPP hn he hx)]
  simp

theorem resAt_of_unramEverywhere {χ : (AE D)ˣ →* Circle} (hχ : UnramEverywhere D χ) (PP : Pl D.host.E) : ResAt χ PP 1 := by
  intro e he x hx hi u hu
  have he' := idemAt_eq he
  have hfu := SpecGood.finUnit_of_res PP (by rw [he']; exact he) x
    (by rw [he']; linear_combination (-1 : AE D) * hx) hi u hu.symm
  rw [hχ x hfu.1 hfu.2.1 hfu.2.2]
  simp

theorem resAt_twist {t : Twist D Circle} (ht : t.Good) {P : Finset (Pl D.host.E)} (h : SplitSet P) (hQ : t.Q ⊆ P)
    {PP : Pl D.host.E} (hPP : PP ∈ P) : ResAt t.chi PP (t.locC PP) := by
  by_cases hq : PP ∈ t.Q
  · have e : t.locC PP = t.resC PP := by simp only [Twist.locC, if_pos hq]
    rw [e]
    exact resAt_of_isResAt (ht.res PP hq)
  · have e : t.locC PP = 1 := by simp only [Twist.locC, if_neg hq]
    rw [e]
    exact resAt_of_unram ht.unram h hQ hPP hq

theorem infPart_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -⟩ := h
  simp [infPart, Algebra.TensorProduct.algebraMap_apply]
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  exact TensorProduct.zero_tmul _ _

theorem infPart_eq_one {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {x : AE D}
    (h : algebraMap (AF D.host.F) (AE D) ε * (x - 1) = x - 1) : infPart D x = 1 := by
  have k := congrArg (infPart D) h
  rw [map_mul, map_sub, map_one, infPart_placeIdem hε, zero_mul] at k
  linear_combination -k

theorem unrOff_of_unram {χ : (AE D)ˣ →* Circle} {P Q : Finset (Pl D.host.E)} (hχ : UnramOutside χ Q) (h : SplitSet Q)
    (hQ : Q ⊆ P) : UnrOff χ P := by
  intro v ε hε hv x h1 h2 h3
  refine hχ x (infPart_eq_one hε h1) h2 h3 ?_
  have k : (idem Q + cA D (idem Q)) * algebraMap (AF D.host.F) (AE D) ε = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [idem, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_eq_zero fun PP hPP => ?_
    obtain ⟨-, -, v', ε', hε', he⟩ := (h.isIdemAt hPP).1
    have hu := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP v' ε' (h.isIdemAt hPP) hε' he
    rw [he, ← map_mul, GlobalTheory.PlaceDatum.placeIdem_mul hε' hε fun e => hv PP (hQ hPP) (hu.trans e), map_zero]
  linear_combination (-(idem Q + cA D (idem Q))) * h1 + ((x : AE D) - 1) * k

theorem unrOff_of_unramEverywhere {χ : (AE D)ˣ →* Circle} (hχ : UnramEverywhere D χ) (P : Finset (Pl D.host.E)) :
    UnrOff χ P := fun _ _ hε _ x h1 h2 h3 => hχ x (infPart_eq_one hε h1) h2 h3

theorem tuple_chars : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ν : Twist D Circle), ν.Good → B.admitted ν.Q →
    (∀ PP ∈ allP B ν.Q, GlobalTheory.StepLaw.ResAt (B.mu * ν.chi) PP (resP B ν PP) ∧
      GlobalTheory.StepLaw.ResAt (B.mu * ν.chi * B.eta⁻¹) PP (resP B ν PP)) ∧
    GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi) (allP B ν.Q) ∧ GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi * B.eta⁻¹) (allP B ν.Q) := by
  intro D S T B hB ν hν hA
  classical
  obtain ⟨P, hPg, hQP, hP⟩ := hA.1.split
  have hsub : allP B ν.Q ⊆ P := Finset.union_subset hPg hQP
  have hdeP : B.de.Q ⊆ P := fun x hx => hQP (Finset.mem_union_left _ hx)
  have hνP : ν.Q ⊆ P := fun x hx => hQP (Finset.mem_union_right _ hx)
  have hη : UnramEverywhere D B.eta := hB.eta.2.1
  have key : ∀ PP ∈ allP B ν.Q, ResAt (B.mu * ν.chi) PP (resP B ν PP) := by
    intro PP hPP
    have hPPP := hsub hPP
    have hνr := resAt_twist hν hP hνP hPPP
    by_cases hg : PP ∈ B.G.Pg
    · have hde : PP ∉ B.de.Q := fun h => Finset.disjoint_left.1 hA.1.disj hg (Finset.mem_union_left _ h)
      have hdl : B.de.locC PP = 1 := by simp only [Twist.locC, if_neg hde]
      rw [resP, if_pos hg, hdl, mul_one]
      exact ResAt.mul (resAt_of_isResAt (hB.tame PP hg)) hνr
    · rw [resP, if_neg hg]
      exact ResAt.mul (ResAt.mul (resAt_of_unram hB.unram hP hPg hPPP hg) (resAt_twist hB.de hP hdeP hPPP)) hνr
  have u1 : UnrOff (B.mu * ν.chi) (allP B ν.Q) :=
    UnrOff.mul (UnrOff.mul (unrOff_of_unram hB.unram (hP.mono hPg) (by intro x hx; simp [allP, hx]))
      (unrOff_of_unram hB.de.unram hB.de.split (by intro x hx; simp [allP, hx])))
      (unrOff_of_unram hν.unram hν.split (by intro x hx; simp [allP, hx]))
  refine ⟨fun PP hPP => ⟨key PP hPP, ?_⟩, u1, u1.mul (unrOff_of_unramEverywhere hη _).inv⟩
  have := (key PP hPP).mul (resAt_of_unramEverywhere hη PP).inv
  rwa [inv_one, mul_one] at this

end GlobalTheory.ExportSeries.TupleChars

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

theorem bc_invTr {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {N : ℕ} (g : GL (Fin N) A) :
    Formalism.UG.bc φ (inside₂ A N g) = inside₂ B N (Formalism.UG.bc φ g) := by
  apply Units.ext
  ext a b
  show φ (((g⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) b a) = (((Formalism.UG.bc φ g)⁻¹ : GL (Fin N) B) : Matrix (Fin N) (Fin N) B) b a
  rw [← map_inv]
  rfl

theorem mapVV_rhoVr {E K : Type} [Field E] [Field K] {ι : Type} [Fintype ι] {n : ℕ} (φ : K →+* ℂ)
    (emb : ι → E →+* K) (lam : ι → DomWeight n) (γ : GL (Fin n) E) (x : VV K lam) :
    mapVV φ lam (rhoVr emb lam γ x) = rhoVr (fun τ => φ.comp (emb τ)) lam γ (mapVV φ lam x) := by
  have h := mapVV_rhoK φ lam (invTrK (embGL emb γ)) x
  refine h.trans (congrArg (fun g : ι → GL (Fin n) ℂ => rhoK lam g (mapVV φ lam x)) ?_)
  funext τ
  show Formalism.UG.bc φ (inside₂ K n (Formalism.UG.bc (emb τ) γ)) = inside₂ ℂ n (Formalism.UG.bc (φ.comp (emb τ)) γ)
  rw [bc_invTr]
  congr 1

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

def conjVV {ι : Type} [Fintype ι] {n : ℕ} (τ : ℂ ≃+* ℂ) (lam : ι → DomWeight n) : VV ℂ lam ≃+ VV ℂ lam where
  toFun := mapVV (τ : ℂ →+* ℂ) lam
  invFun := mapVV (τ.symm : ℂ →+* ℂ) lam
  left_inv x := Subtype.ext (by
    have e : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := by ext z; simp
    rw [mapVV_coe, mapVV_coe, MvPolynomial.map_map, e, MvPolynomial.map_id])
  right_inv x := Subtype.ext (by
    have e : (τ : ℂ →+* ℂ).comp (τ.symm : ℂ →+* ℂ) = RingHom.id ℂ := by ext z; simp
    rw [mapVV_coe, mapVV_coe, MvPolynomial.map_map, e, MvPolynomial.map_id])
  map_add' x y := map_add _ x y

theorem post_mem {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G)
    (ρ : Γ →* Module.End ℂ W) {J J' : Subgroup G} (hJ : J' = J) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (τ : ℂ ≃+* ℂ) (T : W →+ W)
    (hs : ∀ (a : ℂ) w, T (a • w) = τ a • T w) (hρ : ∀ γ w, T (ρ γ w) = ρ γ (T w))
    (hχ : ∀ k (hk : k ∈ J) (hk' : k ∈ J'), ((χ' ⟨k, hk'⟩ : ℂˣ) : ℂ) = τ ((χ ⟨k, hk⟩ : ℂˣ) : ℂ))
    {F : G → W} (hF : F ∈ Bridge.AdForms ι ρ J χ) : (fun g => T (F g)) ∈ Bridge.AdForms ι ρ J' χ' := by
  intro γ h k
  have hk : (k : G) ∈ J := hJ ▸ k.2
  have e := hF γ h ⟨k, hk⟩
  show T (F (ι γ * h * (k : G))) = ((χ' k : ℂˣ) : ℂ) • ρ γ (T (F h))
  have e' : F (ι γ * h * (k : G)) = ((χ ⟨k, hk⟩ : ℂˣ) : ℂ) • ρ γ (F h) := e
  rw [e', hs, hρ, ← hχ k hk k.2]

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

theorem c_rhoVr {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (M : OMDat T.toCore R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v : (R.MW i (sg0 D A)).Vec}
    {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
    (hP : M.Pins κ v ι x₀) (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) (hc : ExtC R i (inC M.c') M.c0' c)
    (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E) (hγ : Bridge.IsRatMat (Vc D i) γ γE) (x : VsV D i ℂ) :
    c (rhoVr (fun τ => D.what₂.embLL.comp (labLL D τ)) (lamV D i) γE x) = (R.cV i).coef.ρ γ (c x) := by
  obtain ⟨gramR, c0R, c0L, hT, hbc⟩ := hP.lift.c0
  have hf : (inC M.c').comp M.jL = D.what₂.embLL := hP.lift.field
  have key : ∀ w : VsV D i D.what₂.LL, c (mapVV D.what₂.embLL (lamV D i) w) = c0L i w := by
    intro w
    obtain ⟨w', hw', hw''⟩ := hbc w
    refine (hc w' _ ?_).trans hw''
    rw [mapVV_coe, hw', MvPolynomial.map_map, hf]
  have hL : c ∘ₗ rhoVr (fun τ => D.what₂.embLL.comp (labLL D τ)) (lamV D i) γE = (R.cV i).coef.ρ γ ∘ₗ c := by
    apply LinearMap.ext_on_range (span_mapVV D.what₂.embLL (lamV D i))
    intro k
    show c (rhoVr (fun τ => D.what₂.embLL.comp (labLL D τ)) (lamV D i) γE (mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) k))) =
      (R.cV i).coef.ρ γ (c (mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) k)))
    rw [← mapVV_rhoVr]
    refine (key _).trans (((hT.mapL i).1 γ γE hγ _).trans ?_)
    exact congrArg _ (key _).symm
  exact LinearMap.congr_fun hL x

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

theorem mapVV_tau_rhoVr (D : D7) (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (hτ : ∀ (φ : D.host.E →+* ℂ) x, τ (φ x) = φ x)
    (γE : GL (Fin (Vc D i).rank) D.host.E) (x : VsV D i ℂ) :
    mapVV (τ : ℂ →+* ℂ) (lamV D i) (rhoVr (fun τ' => D.what₂.embLL.comp (labLL D τ')) (lamV D i) γE x) =
      rhoVr (fun τ' => D.what₂.embLL.comp (labLL D τ')) (lamV D i) γE (mapVV (τ : ℂ →+* ℂ) (lamV D i) x) := by
  rw [mapVV_rhoVr]
  have e : (fun τ' => (τ : ℂ →+* ℂ).comp (D.what₂.embLL.comp (labLL D τ'))) = fun τ' => D.what₂.embLL.comp (labLL D τ') := by
    funext τ'
    ext a
    exact hτ _ a
  rw [e]

theorem exists_conjW {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (M : OMDat T.toCore R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v : (R.MW i (sg0 D A)).Vec}
    {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
    (hP : M.Pins κ v ι x₀) (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) (hc : ExtC R i (inC M.c') M.c0' c)
    (hb : Function.Bijective c) (τ : ℂ ≃+* ℂ) (hτ : ∀ (φ : D.host.E →+* ℂ) x, τ (φ x) = φ x) :
    ∃ TW : (R.cV i).W ≃+ (R.cV i).W, (∀ (a : ℂ) w, TW (a • w) = τ a • TW w) ∧
      (∀ x, TW (c x) = c (mapVV (τ : ℂ →+* ℂ) (lamV D i) x)) ∧
      ∀ γ w, TW ((R.cV i).coef.ρ γ w) = (R.cV i).coef.ρ γ (TW w) := by
  let cb := LinearEquiv.ofBijective c hb
  have hcb : ∀ x, cb.symm (c x) = x := fun x => cb.symm_apply_apply x
  let TW : (R.cV i).W ≃+ (R.cV i).W := cb.symm.toAddEquiv.trans ((conjVV τ (lamV D i)).trans cb.toAddEquiv)
  have hTW : ∀ w, TW w = c (mapVV (τ : ℂ →+* ℂ) (lamV D i) (cb.symm w)) := fun w => rfl
  have hTc : ∀ x, TW (c x) = c (mapVV (τ : ℂ →+* ℂ) (lamV D i) x) := fun x => by rw [hTW, hcb]
  refine ⟨TW, fun a w => ?_, hTc, fun γ w => ?_⟩
  · rw [hTW, hTW, map_smul, map_smulₛₗ, map_smul]
    rfl
  · obtain ⟨x, rfl⟩ := hb.2 w
    obtain ⟨γE, hγ⟩ := GlobalTheory.ConjForms.exists_ratMat (Vc D i) γ
    rw [← c_rhoVr M hP c hc γ γE hγ x, hTc, hTc, mapVV_tau_rhoVr D i τ hτ, c_rhoVr M hP c hc γ γE hγ]

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist


set_option maxHeartbeats 8000000 in
theorem exists_conjForm_equiv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), FixBase T R i τ → ConjTup R τ t t' → ∃ φ : (R.HV i t).H ≃+ (R.HV i t').H, (∀ (a : ℂ) y, φ (a • y) = τ a • φ y) ∧ ∀ y y', ConjForm R i τ c t t' y y' ↔ y' = φ y := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hCore hFW i Tp tup M hPins c hc τ t t' hFix hConj
  have hX := _root_.GlobalTheory.CoefExtC.exists_extC_bijective_unique D G Pl0 T0 A T R F κ v₀ hCore hFW i Tp tup M hPins
  obtain ⟨c₁, -, hb₁, hu⟩ := hX
  have hb : Function.Bijective c :=
    (congrArg (fun f : VsV D i ℂ →ₗ[ℂ] (R.cV i).W => Function.Bijective f) (hu c hc)).mpr hb₁
  have hY := exists_conjW M hPins c hc hb τ hFix.host
  obtain ⟨TW, hs, hTc, hρ⟩ := hY
  have hZ := (_root_.GlobalTheory.ConjRes.conj_res D G Pl0 T0 A T R F κ v₀ hCore τ t t' hConj).2.2.2 i hFix
  obtain ⟨hJ, hχ⟩ := hZ
  have hV := hCore.models.HV i t
  have hV' := hCore.models.HV i t'
  have hs' : ∀ (a : ℂ) w, TW.symm (a • w) = τ.symm a • TW.symm w := by
    intro a w
    apply TW.injective
    rw [hs, TW.apply_symm_apply, TW.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hρ' : ∀ γ w, TW.symm ((R.cV i).coef.ρ γ w) = (R.cV i).coef.ρ γ (TW.symm w) := by
    intro γ w
    apply TW.injective
    refine (TW.apply_symm_apply _).trans ?_
    refine Eq.trans ?_ (hρ γ (TW.symm w)).symm
    exact congrArg _ (TW.apply_symm_apply w).symm
  have hχ' : ∀ k (hk : k ∈ levJ R i t') (hk' : k ∈ levJ R i t),
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨k, hk'⟩ : ℂˣ) : ℂ) =
        τ.symm (((levEnv (Vc D i) (R.βV i) (R.datVt i t')).χ ⟨k, hk⟩ : ℂˣ) : ℂ) := by
    intro k hk hk'
    exact (τ.symm_apply_apply _).symm.trans (congrArg τ.symm (hχ k hk' hk).symm)
  have hmem := fun y => hV.2.1.le (LinearMap.mem_range_self (R.HV i t).e y)
  have hmem' := fun y => hV'.2.1.le (LinearMap.mem_range_self (R.HV i t').e y)
  have hfwd : ∀ y, ∃ y', (R.HV i t').e y' = fun g => TW ((R.HV i t).e y g) := fun y =>
    LinearMap.mem_range.1 (hV'.2.1.ge
      (post_mem (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ _ _ τ TW.toAddMonoidHom hs hρ hχ (hmem y)))
  have hbwd : ∀ y', ∃ y, (R.HV i t).e y = fun g => TW.symm ((R.HV i t').e y' g) := fun y' =>
    LinearMap.mem_range.1 (hV.2.1.ge
      (post_mem (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ.symm _ _ τ.symm TW.symm.toAddMonoidHom hs' hρ' hχ' (hmem' y')))
  choose φ hφ using hfwd
  have hφadd : ∀ y z, φ (y + z) = φ y + φ z := by
    intro y z
    apply hV'.1
    funext g
    have e1 := congrFun (hφ (y + z)) g
    have e2 := congrFun (hφ y) g
    have e3 := congrFun (hφ z) g
    beta_reduce at e1 e2 e3
    refine e1.trans ?_
    exact (congrArg TW (congrFun (map_add (R.HV i t).e y z) g)).trans ((map_add TW _ _).trans
      ((congrArg₂ (· + ·) e2 e3).symm.trans (congrFun (map_add (R.HV i t').e (φ y) (φ z)) g).symm))
  have hφsmul : ∀ (a : ℂ) y, φ (a • y) = τ a • φ y := by
    intro a y
    apply hV'.1
    funext g
    have e1 := congrFun (hφ (a • y)) g
    have e2 := congrFun (hφ y) g
    beta_reduce at e1 e2
    refine e1.trans ?_
    exact (congrArg TW (congrFun (map_smul (R.HV i t).e a y) g)).trans ((hs _ _).trans
      ((congrArg (τ a • ·) e2).symm.trans (congrFun (map_smul (R.HV i t').e (τ a) (φ y)) g).symm))
  have hbij : Function.Bijective φ := by
    constructor
    · intro y z h
      apply hV.1
      funext g
      have := congrFun ((hφ y).symm.trans ((congrArg (R.HV i t').e h).trans (hφ z))) g
      exact TW.injective this
    · intro y'
      obtain ⟨y, hy⟩ := hbwd y'
      refine ⟨y, hV'.1 ?_⟩
      funext g
      exact (congrFun (hφ y) g).trans ((congrArg TW (congrFun hy g)).trans (TW.apply_symm_apply _))
  refine ⟨AddEquiv.ofBijective (AddMonoidHom.mk' φ hφadd) hbij, fun a y => hφsmul a y, fun y y' => ?_⟩
  show ConjForm R i τ c t t' y y' ↔ y' = φ y
  constructor
  · intro hC
    have key : ∀ h, (R.HV i t').e y' (Formalism.IndefR.FWT.fin (Vc D i) h) = TW ((R.HV i t).e y (Formalism.IndefR.FWT.fin (Vc D i) h)) := by
      intro h
      have h0 := hC h
      obtain ⟨x, x', hx, h1, h2⟩ := h0
      have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x := Subtype.ext (hx.trans (GlobalTheory.CoefModel.mapVV_coe _ _ _).symm)
      exact h2.trans ((congrArg c hx').trans ((hTc x).symm.trans (congrArg TW h1.symm)))
    apply hV'.1
    refine Eq.trans ?_ (hφ y).symm
    funext g
    have hs0 := (finHom (Vc D i)).rangeRestrict_surjective g
    obtain ⟨h, hh⟩ := hs0
    exact Eq.subst (motive := fun g => (R.HV i t').e y' g = TW ((R.HV i t).e y g)) hh (key h)
  · rintro rfl h
    have hs1 := hb.2 ((R.HV i t).e y (Formalism.IndefR.FWT.fin (Vc D i) h))
    obtain ⟨x, hx⟩ := hs1
    refine ⟨x, GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x, GlobalTheory.CoefModel.mapVV_coe _ _ _, hx.symm, ?_⟩
    refine (congrFun (hφ y) (Formalism.IndefR.FWT.fin (Vc D i) h)).trans ?_
    exact (congrArg TW hx.symm).trans (hTc x)

end GlobalTheory.ConjTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJointHarmonicOfLoweringStableSubmodule
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section
namespace GlobalTheory.LowerHarm

open MvPolynomial

theorem deg_pderiv_succ {σ : Type} (i : σ) (f : MvPolynomial σ ℂ) (k : ℕ) (h : f.totalDegree ≤ k + 1) :
    (pderiv i f).totalDegree ≤ k := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [pderiv_monomial]
  by_cases h0 : s i = 0
  · simp [h0]
  · refine (totalDegree_monomial_le _ _).trans ?_
    have e : s = (s - Finsupp.single i 1) + Finsupp.single i 1 := by
      rw [tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      omega
    have e2 := congrArg Finsupp.degree e
    rw [map_add (f := _), Finsupp.degree_single] at e2
    have h3 := (le_totalDegree hs).trans h
    change s.degree ≤ k + 1 at h3
    change (s - Finsupp.single i 1).degree ≤ k
    omega

theorem pderiv_of_deg_zero {σ : Type} (i : σ) (f : MvPolynomial σ ℂ) (h : f.totalDegree ≤ 0) : pderiv i f = 0 := by
  rw [totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 h), pderiv_C]

theorem fockT_lower {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : p τ ≤ (i : ℕ)) (hl : (l : ℕ) < p τ) (P : PolF D m n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P = - ∑ j : Fin n, pderiv (τ, i, j) (pderiv (τ, l, j) P) := by
  classical
  have hil : i ≠ l := by intro h; subst h; omega
  have h1 : decide ((i : ℕ) < p τ) = false := decide_eq_false (by omega)
  have h2 : decide ((l : ℕ) < p τ) = true := decide_eq_true hl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT
  rw [Finset.sum_eq_single i, Finset.sum_eq_single l]
  · simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn, h1, h2, hil, LinearMap.sum_apply]
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp

theorem lower_deg {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : p τ ≤ (i : ℕ)) (hl : (l : ℕ) < p τ) (P : PolF D m n) (k : ℕ) (h : P.totalDegree ≤ k + 2) :
    (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P).totalDegree ≤ k := by
  rw [fockT_lower τ p i l hi hl, totalDegree_neg]
  exact totalDegree_finsetSum_le fun j _ => deg_pderiv_succ _ _ _ (deg_pderiv_succ _ _ (k + 1) h)

theorem lower_zero {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : p τ ≤ (i : ℕ)) (hl : (l : ℕ) < p τ) (P : PolF D m n) (h : P.totalDegree ≤ 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P = 0 := by
  rw [fockT_lower τ p i l hi hl]
  simp [pderiv_of_deg_zero _ _ (deg_pderiv_succ _ _ 0 h)]

theorem lower_to_harmonic : ∀ (D : D7) (n m : ℕ) (p : D.what₂.Tau → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (M : Submodule ℂ (W →ₗ[ℂ] PolF D m n)), (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (i l : Fin m), p τ ≤ (i : ℕ) → (l : ℕ) < p τ → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ∈ M) → M ≠ ⊥ → ∃ ψ ∈ M, ψ ≠ 0 ∧ ∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (ψ w') = 0 := by
  intro D n m p W _ _ _ M hM hne
  classical
  have hex : ∃ d, ∃ ψ ∈ M, ψ ≠ 0 ∧ ∀ w, (ψ w).totalDegree ≤ d := by
    obtain ⟨ψ, hψ, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    let b := Module.finBasis ℂ W
    refine ⟨Finset.univ.sup fun j => (ψ (b j)).totalDegree, ψ, hψ, hψ0, fun w => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr w, map_sum]
    refine totalDegree_finsetSum_le fun j _ => ?_
    rw [map_smul]
    exact (totalDegree_smul_le _ _).trans
      (Finset.le_sup (f := fun j => (ψ (b j)).totalDegree) (Finset.mem_univ j))
  obtain ⟨ψ, hψ, hψ0, hdeg⟩ := Nat.find_spec hex
  refine ⟨ψ, hψ, hψ0, fun w τ i l hi hl => ?_⟩
  by_contra hne'
  have hL := hM ψ hψ τ i l hi hl
  have hL0 : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ≠ 0 := fun h => hne' (by simpa using LinearMap.congr_fun h w)
  rcases Nat.lt_or_ge (Nat.find hex) 2 with h2 | h2
  · exact hne' (lower_zero τ p i l hi hl _ (by have := hdeg w; omega))
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 2 := ⟨Nat.find hex - 2, by omega⟩
    have := Nat.find_min' hex ⟨_, hL, hL0, fun w' => lower_deg τ p i l hi hl _ k (hk ▸ hdeg w')⟩
    omega

end GlobalTheory.LowerHarm
end
end

