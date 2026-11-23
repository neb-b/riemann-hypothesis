module

public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ImageLcv
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FWCentral
section
noncomputable section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.JoinChr Formalism.IndefR.Links
  Formalism.IndefR.Arith Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {D : D7}


end Loc

section Frame

open ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7}

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

variable {M}


end Frame

section Cut

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)


end Cut

section Central

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G0 : Type} [Group G0] [Fintype G0] (A : FormsL LL Ks WL W G0)

variable {ζ : LLˣ} {z : G0}

end Central

section Mat

open Formalism.IndefR.Cx Formalism.L2.Indef

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool)
  (i : Fin D.R.m)

theorem principal_form_tensor_expansion (c : Fin (finrank D.what₂.LL (R.toRealDat.WL F.lv2 b i)) → ℂ) :
    Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).w0C b i c) =
      ∑ l, cj (twAt D.what₂.embLL A3.A.v0) (c l) • (R.FW i).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 b i l) := by
  have hnP : ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < RealDat.nP F.lv2 b := by unfold RealDat.nP; exact_mod_cast Nat.card_pos
    exact_mod_cast (Real.sqrt_pos.2 this).ne'
  show ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).subtype
    (∑ l, cj (twAt D.what₂.embLL A3.A.v0) (c l) •
      (⟨R.toRealDat.bC F.lv2 b i _ l, Submodule.subset_span ⟨l, rfl⟩⟩ : R.toRealDat.WS F.lv2 b i (sg0 D A3.A))) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [LinearMap.map_smul, smul_comm]
  congr 1
  show ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • (((Real.sqrt (RealDat.nP F.lv2 b))⁻¹ : ℝ) : ℂ) •
    (R.FW i).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 b i l) = _
  rw [smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hnP, one_smul]

end Mat

section CC

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]
  {D : D7} {V : HSp D} {σ0 : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ0 r} {dict : GA D V → Σ k, Frame (U.X k).Ψ r}
  {mu : GA D V → ℂ} {xr : ℝ} {a : (E →+* ℂ) × ℕ → ℕ} {G : Type} [Group G] {act : G → Rul Xo c →ₗ[c.F] Rul Xo c} {Tup : Type}
  {dδ : Tup → DeltaDat Xo c n} {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)]
  {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c.F} {La : ∀ t, Cl' t → GenLat E n} {Nc gam : ∀ t, Cl' t → ℕ}
  {vol : Tup → c.F} {ep : ∀ t, Cl' t → c.F} {io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F}
  {thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop} {LL : IntermediateField ℚ ℂ}
  {Cu : Submodule c.F (Rul Xo c)} {cc cc' : U.Comp → ℂ} {ph ph' : ℂ}




end CC

section CCTie

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} {hle : c.F ≤ c'.F} {n r : ℕ} {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]
  {LL : IntermediateField ℚ ℂ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ0' : c'.F →+* ℂ} {D : D7} {V : HSp D}
  {dict : GA D V → Σ k, Frame ((unfBC hle U σ0').X k).Ψ r} {mu : GA D V → ℂ} {xr : ℝ} {a : (E →+* ℂ) × ℕ → ℕ}
  {G : Type} [Group G] {act : G → Rul Xo c →ₗ[c.F] Rul Xo c} {act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c'} {Tup : Type}
  {dδ : Tup → DeltaDat Xo c' n} {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)]
  {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F} {La : ∀ t, Cl' t → GenLat E n} {Nc gam : ∀ t, Cl' t → ℕ}
  {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F} {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
  {thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop} {cc cc' : (unfBC hle U σ0').Comp → ℂ} {ph ph' : ℂ}

end CCTie

section CCDat

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

end CCDat

section Phase

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem phiC_zero {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    phiC T hV a 0 = 0 := by
  subst hV
  show T.phiJ j σ a 0 = 0
  rw [CoreJ.phiJ, map_zero, map_zero, smul_zero]

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem phiC_apply {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (h : σ = σ') {W : HSp D} (hV : T.V j σ = W) (hV' : T.V j σ' = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D W) :
    phiC T hV a f g = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * adel W (castDict hV' (T.dict j σ'))
      (muPin W (castDict hV' (T.dict j σ')) (castDict hV' (T.mu j σ')) (T.cE j σ')) (rdU (T.U j σ') f) g := by
  subst h
  subst hV
  rfl

theorem FWTie.evaluates_of_lUnif (t : FWTie T R κ v₀) (hU : R.LUnif) : t.Evaluates := by
  intro i σ hσ hV
  refine t.ev i σ hσ hV (Classical.byContradiction fun hn => hn ⟨0, fun f => ?_⟩)
  have h0 := t.ev0 i σ hσ hV hn
  have h1 := (hU i σ).1 _ _ (Pi.basisFun D.what₂.LL (Fin (R.nW i))).linearIndependent
  have h2 : ((t.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = 0 :=
    funext fun k => absurd (by rw [h0]; rfl) (h1.ne_zero k)
  have h3 : f = 0 := (t.e i).map_eq_zero_iff.1 (Subtype.ext h2)
  subst h3
  exact (congrArg (fun F : MMap (R.MW i σ) => F (v₀ i σ)) (R.HW i σ).e.map_zero).trans (phiC_zero hV _).symm

theorem FWTie.rat_of_val (t : FWTie T R κ v₀) (ht : t.Evaluates) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (hσ : GoodEmb T.Q.c (res T σ))
    (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (hinj : Function.Injective (evAt R i σ (v₀ i σ))) {w : (R.HW i σ).H} {n : ℕ}
    (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κ i)
    (h : ∀ g, evAt R i σ (v₀ i σ) w g = ∑ k, σ (a k) * phiC T hV (wtA (κ i)) (f k : T.R ((i : ℕ) + 1)) g) :
    ∃ y, (R.FW i).j σ y = w := by
  refine ⟨∑ k, a k • ((t.e i (f k) : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL), hinj (funext fun g => ?_)⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h g, evAt, map_sum, map_sum, _root_.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ, map_smul, ← ht i σ hσ hV (f k)]
  rfl

theorem baseEmbedding_restriction_eq_coefficientInclusion (t : FWTie T R κ v₀) {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) :
    res T (sg0 D A) = O.s0 :=
  (congrArg (res T) (sgAt_mk _ R.hv0)).trans ((res_embLL T t.alg_eq t.laws.pins.2.2.1).trans (sOv_eq T.toCore O.c' O.hle).symm)

theorem phi_eq_phiC {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) {σ : T.Q.c.F →+* ℂ} (hs : σ = O.s0)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (g : GA D (Wc D i)) :
    (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * O.phi (T.cE ((i : ℕ) + 1) O.s0) f g = phiC T hV a f g :=
  (phiC_apply hs hV O.hV a f g).symm

theorem evAt_smul (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) (c : ℂ) (w : (R.HW i σ).H) (g : GA D (Wc D i)) :
    evAt R i σ v (c • w) g = c * (R.HW i σ).e w v g := by
  rw [evAt, map_smul]
  rfl

theorem phase_of_phRat (t : FWTie T R κ v₀) (hU : R.LUnif) {i : Fin D.R.m}
    (hinj : Function.Injective (evAt R i (sg0 D A) (v₀ i (sg0 D A)))) {Tp : Type} {tup : Tp → T0}
    (O : OMDat T.toCore R i Tp tup) {ph : ℂ} (h : O.PhRat (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O.s0) ph)
    (x : A.fam.amb.FL i A.μ0) : ∃ y, (R.FW i).j (sg0 D A) y = ph • R.thG i A.μ0 (R.jV i A.μ0 x) :=
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) (baseEmbedding_restriction_eq_coefficientInclusion t O)).trans O.hV
  have hg : ∀ y, D.what₂.embLL y = sg0 D A y := fun y => (DFunLike.congr_fun (sgAt_mk _ R.hv0) y).symm
  (h x).elim fun _ h1 => h1.elim fun a h2 => h2.elim fun f hf =>
    t.rat_of_val (t.evaluates_of_lUnif hU) (base_embedding_good T R t.alg_eq t.laws.pins.2.2.1) hV hinj a f fun g =>
      (evAt_smul i _ _ ph _ g).trans ((hf g).trans (Finset.sum_congr rfl fun _ _ =>
        congrArg₂ (· * ·) (hg _) (phi_eq_phiC O (baseEmbedding_restriction_eq_coefficientInclusion t O) hV _ _ g)))

theorem phase_of_oneMap (t : FWTie T R κ v₀) (hU : R.LUnif) {i : Fin D.R.m}
    (hinj : Function.Injective (evAt R i (sg0 D A) (v₀ i (sg0 D A)))) {Tp : Type} {tup : Tp → T0}
    (O : OMDat T.toCore R i Tp tup) {ph : ℂ} (h : O.OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O.s0) ph) :
    ‖ph‖ = 1 ∧ ∀ x, ∃ y, (R.FW i).j (sg0 D A) y = ph • R.thG i A.μ0 (R.jV i A.μ0 x) :=
  ⟨h.2.1.2.2.2.2.1, phase_of_phRat t hU hinj O h.2.2⟩

end Phase

end Formalism.IndefR.FWT
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
section
noncomputable section

open NumberField
open scoped TensorProduct

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

def ActKeeps (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m) : Prop :=
  ∀ g, ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev T.Q.c (O i).lev2 g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n

def RhoGeo (fw : FWTie T R κ v₀) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) : Prop :=
  ∀ i : Fin D.R.m,
    (ActKeeps (κ := κ) O i → ActRho R i (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) (fw.e i) (actLev T.Q.c (O i).lev2)) ∧
      (¬ ActKeeps (κ := κ) O i → ∀ g, (R.FW i).ρ g = 1)

end Formalism.IndefR.FWT
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.WeakCharacterisationWithError
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Err

open Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat3

def withErr (R : RealDat3 D A3 Ks) (e : type_of% R.err0) : RealDat3 D A3 Ks :=
  { R with toRealDat := { R.toRealDat with err0 := e } }

variable {R : RealDat3 D A3 Ks} {F : Face3 D A3}

def _root_.Formalism.IndefR.Links.reErr {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Am : DefAmb Bs}
    (X : CxData Am) (e : type_of% X.err0) : CxData Am := { X with err0 := e }

theorem partAt_withErr (e i p v) : (R.withErr e).PartAt F i p v ↔ R.PartAt F i p v := by
  exact Iff.rfl

theorem zs_withErr (e) : ((R.withErr e).toCx3 F).zs = (R.toCx3 F).zs := by
  rfl


set_option maxHeartbeats 1000000 in
theorem weak_characterisation_with_error (h : R.WeakCharacterisation F) (e) : (R.withErr e).WeakCharacterisation F := by
  cases_type* RealDat3.WeakCharacterisation RealDat.BaseW RealDat.IsGrp RealDat.IsFam RealDat.IsModels RealDat.IsChainW RealDat.IsThPW RealDat3.IsInert RealDat3.IsScal RealDat3.IsTup
  repeat' (first | assumption | constructor)

end RealDat3

end Err

section Three

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull Formalism.IndefR.Fin Formalism.IndefR.Eqv

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {F : Face3 D A3}

namespace RealDat3

variable (R : RealDat3 D A3 Ks)

def updS (kap : ℝ) (lam : type_of% R.lam3) : RealDat3 D A3 Ks :=
  { R with toRealDat := R.toRealDat.upd6 kap R.lam, lam3 := lam }

def Eig0 (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix) (l : ℝ) : Prop :=
  R.Wp3 i p ≠ ⊥ ∧ ∀ x ∈ R.Wp3 i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x


variable (F) in
def EigOff (i : Fin D.R.m) (p : A3.fam3.base3.Ix) (v : InfinitePlace D.what₂.LL) (l : ℝ) : Prop :=
  PartX F.cr (R.toCx3 F) false i p v ∧ SimX F.cr (R.toCx3 F) false i p v l

variable {R}

theorem base_eigenvalue_unique {i t p} (l l' : ℝ) (h : R.Eig0 i t p l) (h' : R.Eig0 i t p l') : l = l' := by
  obtain ⟨hb, hl⟩ := h
  obtain ⟨-, hl'⟩ := h'
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have hxx : (l : ℂ) • x = (l' : ℂ) • x := (hl x hx).symm.trans (hl' x hx)
  have hc : (l : ℂ) = (l' : ℂ) := by
    by_contra hne
    apply hx0
    have hne' : (l : ℂ) - (l' : ℂ) ≠ 0 := sub_ne_zero.mpr hne
    have h0 : ((l : ℂ) - (l' : ℂ)) • x = 0 := by rw [sub_smul, hxx, sub_self]
    calc x = ((l : ℂ) - (l' : ℂ))⁻¹ • (((l : ℂ) - (l' : ℂ)) • x) := by
          rw [smul_smul, inv_mul_cancel₀ hne', one_smul]
      _ = 0 := by rw [h0, smul_zero]
  exact_mod_cast hc

theorem eigOff_unique {i p v} (l l' : ℝ) (h : R.EigOff F i p v l) (h' : R.EigOff F i p v l') : l = l' := by
  obtain ⟨⟨x, hx, hm⟩, hs⟩ := h
  obtain ⟨-, hs'⟩ := h'
  have e1 := hs x hx x
  have e2 := hs' x hx x
  have hc : ((l : ℝ) : ℂ) = ((l' : ℝ) : ℂ) := mul_right_cancel₀ hm (e1.symm.trans e2)
  exact_mod_cast hc

theorem partAt_updS (kap lam i p v) : (R.updS kap lam).PartAt F i p v ↔ PartX F.cr (R.toCx3 F) false i p v := by
  exact Iff.rfl

theorem sim_updS (kap lam i p v l) : SimX F.cr ((R.updS kap lam).toCx3 F) false i p v l ↔ SimX F.cr (R.toCx3 F) false i p v l := by
  exact Iff.rfl

theorem zs_updS (kap lam) : ((R.updS kap lam).toCx3 F).zs = (R.toCx3 F).zs := by
  rfl

end RealDat3


open Classical in
theorem scalars_exist (R : RealDat3 D A3 Ks) : ∃ kap lam, (R.updS kap lam).IsScal F := by

  have hcan : ∀ {N : Type} [AddCommGroup N] [Module ℂ N] {a b : ℂ} {x : N}, x ≠ 0 → a • x = b • x → a = b := by
    intro N _ _ a b x hx h
    by_contra hne
    apply hx
    have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h0 : (a - b) • x = 0 := by rw [sub_smul, h, sub_self]
    calc x = (a - b)⁻¹ • ((a - b) • x) := by rw [smul_smul, inv_mul_cancel₀ hne', one_smul]
      _ = 0 := by rw [h0, smul_zero]

  obtain ⟨lam, hlam⟩ : ∃ lam : Fin D.R.m → T → A3.fam3.base3.Ix → InfinitePlace D.what₂.LL → ℝ,
      ∀ i t p v, lam i t p v =
        if v = A3.A.v0 then
          (if h : ∃ l, R.Eig0 i t p l then h.choose else Real.exp ((F.Zsc (R.toCx3 F).zs).l6m i))
        else
          (if h : ∃ l, R.EigOff F i p v l then h.choose else Real.exp ((F.Zsc (R.toCx3 F).zs).l6m i)) :=
    ⟨_, fun _ _ _ _ => rfl⟩

  obtain ⟨kap, hkap⟩ : ∃ kap : ℝ, ∀ κ : ℝ,
      Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 (R.updS 0 lam).lamN κ →
      (∃ t p, R.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p ≠ 0) → kap = κ := by
    by_cases hex : ∃ κ : ℝ,
        Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 (R.updS 0 lam).lamN κ ∧
        (∃ t p, R.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p ≠ 0)
    · obtain ⟨κ0, hk0, -⟩ := hex
      refine ⟨κ0, fun κ hk hnd => ?_⟩
      obtain ⟨t, p, hE, hP⟩ := hnd
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE
      have e := hcan hx0 ((hk0 t p x hx).symm.trans (hk t p x hx))
      have e' : κ0 * ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p =
          κ * ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p := by exact_mod_cast e
      exact mul_right_cancel₀ hP e'
    · exact ⟨0, fun κ hk hnd => absurd ⟨κ, hk, hnd⟩ hex⟩
  refine ⟨kap, lam, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i t p l hb hl
    have hE : R.Eig0 i t p l := ⟨hb, hl⟩
    show lam i t p A3.A.v0 = l
    rw [hlam, if_pos rfl, dite_eq_left ⟨l, hE⟩]
    exact RealDat3.base_eigenvalue_unique (R := R) _ _ (Exists.choose_spec _) hE
  · intro κ hk hnd
    exact hkap κ hk hnd
  · intro i p v l hv hP hS
    have hPX : PartX F.cr (R.toCx3 F) false i p v := (RealDat3.partAt_updS kap lam i p v).1 hP
    have hSX : SimX F.cr (R.toCx3 F) false i p v l := (RealDat3.sim_updS kap lam i p v l).1 hS
    have hE : R.EigOff F i p v l := ⟨hPX, hSX⟩
    show lam i A3.A.μ0 p v = l
    rw [hlam, if_neg hv, dite_eq_left ⟨l, hE⟩]
    exact RealDat3.eigOff_unique (R := R) _ _ (Exists.choose_spec _) hE
  · intro i t p hb
    show lam i t p A3.A.v0 = Real.exp ((F.Zsc ((R.updS kap lam).toCx3 F).zs).l6m i)
    rw [RealDat3.zs_updS, hlam, if_pos rfl, dite_eq_right]
    rintro ⟨l, hl⟩
    exact hl.1 hb
  · intro i p v hv hnP
    show lam i A3.A.μ0 p v = Real.exp ((F.Zsc ((R.updS kap lam).toCx3 F).zs).l6m i)
    rw [RealDat3.zs_updS, hlam, if_neg hv, dite_eq_right]
    rintro ⟨l, hl⟩
    exact hnP ((RealDat3.partAt_updS kap lam i p v).2 hl.1)
  · intro i t p v hv
    show lam i t p v = lam i A3.A.μ0 p v
    rw [hlam, hlam, if_neg hv, if_neg hv]


end Three

end Formalism.IndefR.Links

end
end

