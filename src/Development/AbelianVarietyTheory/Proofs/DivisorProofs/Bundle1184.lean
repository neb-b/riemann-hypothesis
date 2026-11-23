module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPairSpecializesDiagonalGenericPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPair_specializes_diagonal_genericPoint : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K), GenPair Y ψ₁ ψ₂ → ∃ h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str, Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h (IsLocalRing.closedPoint K) ⤳ Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
  first | exact @GlobalTheory.FlagPush.genPair_specializes_diagonal | exact GlobalTheory.FlagPush.genPair_specializes_diagonal | (intros; apply GlobalTheory.FlagPush.genPair_specializes_diagonal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericSubquotientPrincipalSeries
section
open NumberField IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CuspDetBlocks

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.Whittaker


open GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic in
theorem exists_isGeneric_subrep {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (P : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (S : Subrepresentation (P.locRep w)) (hS : S.toSubmodule ≠ ⊥) :
    ∃ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ ∧ ψ ≠ 1 ∧ IsGeneric ψ S.toRepresentation := by
  obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.CuspGeneric.exists_stdPsi E
  have hg : ∀ v : P.V, Good ψ (a - 1) v.1.1 := fun v => _root_.GlobalTheory.CuspGeneric.good_of_isCuspForm E a ψ v.1 (P.cusp _ v.2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨v₀, hv₀S, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hv1 : v₀.1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h, gw, e, hc⟩ := _root_.GlobalTheory.CuspGeneric.exists_split_loc E a w g₀
  have hrt : ∀ u (v : P.V) x, whit ψ (a - 1) (P.locRep w u v).1.1 x =
      whit ψ (a - 1) v.1.1 (x * finGL E a (locGL E a w u)) := fun u v x => whit_rt _ _ _ _
  let l : P.V →ₗ[ℂ] ℂ :=
    { toFun := fun v => whit ψ (a - 1) v.1.1 h
      map_add' := fun v v' => congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => congrFun (whit_smul (a - 1) c v.1.1) h }
  have hl : ∀ v, l v = whit ψ (a - 1) v.1.1 h := fun _ => rfl
  have hne : l (P.locRep w gw v₀) ≠ 0 := by
    rw [hl, hrt, ← e]
    exact hg₀
  have hlaw : ∀ u ∈ unipB (w.adicCompletion E) (Fin a), ∀ v : P.V,
      l (P.locRep w u v) = (locPsi hψ w (superDiag u) : ℂ) * l v := fun u hu v => by
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
    obtain ⟨t1, t2, t3⟩ := _root_.GlobalTheory.CuspRep.locTri_adelic E a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hl, hrt, hc, this, t3, superDiag_eq_sum_pairs]
    rfl
  have hcont : Continuous (locPsi hψ w) := by
    refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)).comp
      (CuspSub.continuous_sLoc w)
  have hne1 : locPsi hψ w ≠ 1 := fun h1 => by
    obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  refine ⟨locPsi hψ w, hcont, hne1, l ∘ₗ S.toSubmodule.subtype, fun e' => hne ?_, fun u hu v => ?_⟩
  · exact LinearMap.congr_fun e' ⟨_, S.apply_mem_toSubmodule gw hv₀S⟩
  · exact hlaw u hu v.1

end GlobalTheory.CuspDetBlocks

namespace GlobalTheory.CuspDetBlocks

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.Whittaker

end GlobalTheory.CuspDetBlocks
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodScalarOfIsAdelicScalar
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftScalarCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Source

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem span_jVx (hV : R.models_HV) (hj : R.models_jV) : Submodule.span ℂ (Set.range (jVx R i A.μ0)) = ⊤ := by
  have h0 : (R.HV i A.μ0).e '' Set.range (jVx R i A.μ0) = Set.range (R.B.jL i A.μ0) :=
    (Set.range_comp _ _).symm.trans (congrArg Set.range (funext (hj i A.μ0)))
  have h1 : (Submodule.span ℂ (Set.range (jVx R i A.μ0))).map (R.HV i A.μ0).e = (⊤ : Submodule ℂ _).map (R.HV i A.μ0).e :=
    ((Submodule.map_span _ _).trans (congrArg (Submodule.span ℂ) h0)).trans
      ((GlobalTheory.PresBasic.ext_span (R.B.L i A.μ0).pres).trans ((hV i A.μ0).2.1.symm.trans (LinearMap.range_eq_map _)))
  exact Submodule.map_injective_of_injective (hV i A.μ0).1 h1

end Source

section Target

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem eval_inj (hW : R.models_HW) {v₀ : (R.MW i (sg0 D A)).Vec} (hv : IsChosenExtremalVector R i (sg0 D A) v₀) {x y : (R.HW i (sg0 D A)).H}
    (h : (R.HW i (sg0 D A)).e x v₀ = (R.HW i (sg0 D A)).e y v₀) : x = y := by
  have h0 : (R.HW i (sg0 D A)).e (x - y) v₀ = 0 := by
    rw [LinearMap.map_sub]
    exact sub_eq_zero.2 h
  have h1 := (hW i (sg0 D A)).2.2 (x - y) (x - y)
  rw [ipAt, GlobalTheory.EvalAtUnitVector.ipM_self_eq_zero _ _ _ _ v₀ (IsChosenExtremalVector.norm R hv) h0, mul_zero] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

theorem eC_idem (hr : R.grp_record) : GoodBasisCentralIdempotents.IsCentralIdem (RealDat.eC (A := A) (sg0 D A)) := by
  obtain ⟨eR, _, _, h, _⟩ := hr
  have h0 : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have h1 : ∀ g, RealDat.eC (A := A) (sg0 D A) g = D.ntypes.e0.coeff (eR g) := fun g => by rw [h0]; exact h g
  obtain ⟨h2, h3⟩ := GlobalTheory.GoodLatCompare.isCentralIdempotent_of_goodSeriesIdempotent (D := D) (RingHom.id ℂ) (eC := fun g => D.ntypes.e0.coeff g) fun _ => rfl
  refine ⟨fun g k => ?_, fun g => ?_⟩
  · rw [h1, h1, map_mul eR, map_mul eR, map_inv eR]
    exact h2 _ _
  · rw [h1]
    refine Eq.trans (Fintype.sum_equiv eR.toEquiv _ _ fun k => ?_) (h3 (eR g))
    rw [h1, h1, map_mul eR, map_inv eR]
    rfl

theorem postOn_of_good {P : LevelP R.Pg D.R.r ℂ} {U : MMap (R.MW i (sg0 D A))} (hU : U ∈ R.Wat i (sg0 D A) P) :
    postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) U = U :=
  sub_eq_zero.1 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hU).2)

end Target

section Geometric

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

structure DictFacts : Prop where
  dom : ∀ g, (O.dict g).2 ∈ ((C.U ((i : ℕ) + 1) O.s0).X (O.dict g).1).dom
  mu : ∀ g, ‖O.mu g‖ = 1
  cc : ∀ k, ‖cc k‖ = 1
  lifts : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv)

variable {O cc} (hd : DictFacts O cc)
include hd

omit hd

variable (O cc)

variable {O cc}

include hd

omit hd

end Geometric

section Main

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

variable {T R F κ v₀ O}

variable (T R F κ v₀ O)

end Main

end GlobalTheory.LiftScalarCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtPosDef
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.FockPos

variable {D : D7}

def frAt {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  fr.1.map (tauE D τ)

def zCo (θ : InfFam D) {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (w : WO S T) :
    Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank :=
  fun τ => (frAt frT τ)⁻¹ * compAt θ τ w * frAt frS τ

def gaussO (θ : InfFam D) {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (w : WO S T) : ℂ :=
  Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ))

theorem cartan_eq_one {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) (hG : G.PosDef) : s = 1 := by
  obtain ⟨hss, -, hP⟩ := h
  have key : ∀ v : Fin k → ℂ, (s - 1) *ᵥ v = 0 := by
    intro v
    by_contra hx
    set x := (s - 1) *ᵥ v with hxdef
    have hsx : s *ᵥ x = -x := by
      rw [hxdef, Matrix.mulVec_mulVec, Matrix.mul_sub, hss, Matrix.mul_one, ← neg_sub, Matrix.neg_mulVec]
    have h1 := hP.dotProduct_mulVec_pos hx
    have h2 := hG.dotProduct_mulVec_pos hx
    rw [← Matrix.mulVec_mulVec, hsx, Matrix.mulVec_neg, dotProduct_neg] at h1
    have := add_pos h1 h2
    simp at this
  have : s - 1 = 0 := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  exact sub_eq_zero.1 this

theorem frAt_det_ne {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) : (frAt fr τ).det ≠ 0 := by
  have e : (frAt fr τ).det = tauE D τ fr.1.det := (RingHom.map_det (tauE D τ) fr.1).symm
  rw [e, map_ne_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 fr.isUnit).ne_zero

theorem frAt_on {S : HSp D} (fr : GL (Fin S.rank) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1) (τ : D.what₂.Tau) :
    (frAt fr τ)ᴴ * gramAt D S τ * frAt fr τ = 1 := by
  have hs : ∀ x : D.host.E, tauE D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = star (tauE D τ x) := fun x => by
    have := D.host.isCMField_hostE
    exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ x
  have h2 := congrArg (fun M => M.map (tauE D τ)) h
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  rw [← h2, frAt, gramAt]
  congr 2
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  exact (hs _).symm

theorem gramAt_posDef {S : HSp D} (fr : GL (Fin S.rank) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1) (τ : D.what₂.Tau) :
    (gramAt D S τ).PosDef := by
  have hMd : IsUnit (frAt fr τ).det := isUnit_iff_ne_zero.2 (frAt_det_ne fr τ)
  have hM : IsUnit (frAt fr τ) := (Matrix.isUnit_iff_isUnit_det _).2 hMd
  have hMHd : IsUnit (frAt fr τ)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hMd.star
  have h1 := frAt_on fr h τ
  have e : ((frAt fr τ)⁻¹)ᴴ * 1 * (frAt fr τ)⁻¹ = gramAt D S τ := by
    calc ((frAt fr τ)⁻¹)ᴴ * 1 * (frAt fr τ)⁻¹
        = ((frAt fr τ)ᴴ)⁻¹ * ((frAt fr τ)ᴴ * gramAt D S τ * frAt fr τ) * (frAt fr τ)⁻¹ := by
          rw [h1, Matrix.conjTranspose_nonsing_inv]
      _ = (((frAt fr τ)ᴴ)⁻¹ * (frAt fr τ)ᴴ) * gramAt D S τ * (frAt fr τ * (frAt fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = gramAt D S τ := by
          rw [Matrix.nonsing_inv_mul _ hMHd, Matrix.mul_nonsing_inv _ hMd, Matrix.one_mul, Matrix.mul_one]
  rw [← e]
  refine Matrix.PosDef.one.conjTranspose_mul_mul_same ?_
  exact Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hM)

theorem cart_one {S : HSp D} (fr : GL (Fin S.rank) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1)
    {s : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} (hs : ∀ τ, IsCartanInv (gramAt D S τ) (s τ)) : s = fun _ => 1 := by
  funext τ
  have h1 : (gramAt D S τ).PosDef := gramAt_posDef fr h τ
  exact cartan_eq_one (hs τ) h1

end GlobalTheory.FockPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphJetsMemPowSupUniformiserStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graphJets_mem_pow_sup_uniformiser : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  graphIdeal E R π ρ ≤ 𝔭 → Irreducible t →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i →
    ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
    w ∈ 𝔭 ^ M ⊔ Ideal.span {⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩} := by
  first | exact @GlobalTheory.GraphLocal.jets_mem_pow_sup | exact GlobalTheory.GraphLocal.jets_mem_pow_sup | (intros; apply GlobalTheory.GraphLocal.jets_mem_pow_sup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureUniqueSigmaCompactNormalisedCompactOp
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory

theorem haar_unique_of_sigmaCompact_normalised :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
    (K : ℕ → Set G), (∀ j, IsCompact (K j) ∧ MeasurableSet (K j)) → (⋃ j, K j) = Set.univ →
    ∀ (s : Set G) (c : ENNReal), IsOpen s → IsCompact s → s.Nonempty → ν s = c * μ s → ν = c • μ := by
  intro G _ _ _ _ _ _ μ ν _ _ _ K hK hcov s c hso hsc hsn hνs
  have key : ∀ A : Set G, IsCompact (closure A) →
      ν A = (Measure.haarScalarFactor ν μ : ENNReal) * μ A := fun A hA => by
    have := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure ν μ hA
    rw [this, ENNReal.smul_def, smul_eq_mul]
  have hs0 : μ s ≠ 0 := (hso.measure_pos μ hsn).ne'
  have hstop : μ s ≠ ⊤ := hsc.measure_lt_top.ne
  have hc : c = (Measure.haarScalarFactor ν μ : ENNReal) := by
    have h1 := key s (hsc.closure_of_subset subset_rfl)
    rw [hνs] at h1
    exact (ENNReal.mul_left_inj hs0 hstop).mp h1
  subst hc
  ext A hA
  let B : ℕ → Set G := fun j => A ∩ Set.accumulate K j
  have hBmono : Monotone B := fun i j hij => Set.inter_subset_inter_right _ (Set.monotone_accumulate hij)
  have hBcl : ∀ j, IsCompact (closure (B j)) := fun j =>
    (isCompact_accumulate (fun i => (hK i).1) j).closure_of_subset Set.inter_subset_right
  have hBU : (⋃ j, B j) = A := by
    simp only [B, ← Set.inter_iUnion, Set.iUnion_accumulate, hcov, Set.inter_univ]
  rw [← hBU, hBmono.measure_iUnion, hBmono.measure_iUnion]
  simp only [Measure.smul_apply, smul_eq_mul]
  exact iSup_congr fun j => key _ (hBcl j)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumSu21RankOneSeriesDifferences
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory.SURankOneSeries

theorem term_even (q z : ℂ) (hq : q ≠ 0) (i : ℕ) :
    (z / q ^ 2) ^ (2 * i) * q ^ (2 * i + 2 * (2 * i / 2)) = (z ^ 2) ^ i := by
  have h : 2 * i / 2 = i := by omega
  rw [h, div_pow, ← pow_mul, show 2 * i + 2 * i = 2 * (2 * i) by ring, ← pow_mul]
  field_simp

theorem term_odd (q z : ℂ) (hq : q ≠ 0) (i : ℕ) :
    (z / q ^ 2) ^ (2 * i + 1) * q ^ (2 * i + 1 + 2 * ((2 * i + 1) / 2)) = z / q * (z ^ 2) ^ i := by
  have h : (2 * i + 1) / 2 = i := by omega
  rw [h]
  have h4 : 2 * i + 1 + 2 * i = 2 * (2 * i) + 1 := by ring
  rw [h4]
  simp only [div_pow, ← pow_mul]
  rw [show 2 * (2 * i + 1) = (2 * (2 * i) + 1) + 1 by ring, pow_succ q (2 * (2 * i) + 1)]
  field_simp
  ring

theorem hasSum_weighted (q z : ℂ) (hq : q ≠ 0) (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ => (z / q ^ 2) ^ j * q ^ (j + 2 * (j / 2))) ((1 + q⁻¹ * z) / (1 - z ^ 2)) := by
  have hz2 : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg z]
  have hg := hasSum_geometric_of_norm_lt_one hz2
  have he : HasSum (fun k : ℕ => (z / q ^ 2) ^ (2 * k) * q ^ (2 * k + 2 * (2 * k / 2))) (1 - z ^ 2)⁻¹ := by
    have : (fun k : ℕ => (z / q ^ 2) ^ (2 * k) * q ^ (2 * k + 2 * (2 * k / 2))) = fun k => (z ^ 2) ^ k :=
      funext fun k => term_even q z hq k
    rw [this]; exact hg
  have ho : HasSum (fun k : ℕ => (z / q ^ 2) ^ (2 * k + 1) * q ^ (2 * k + 1 + 2 * ((2 * k + 1) / 2)))
      (z / q * (1 - z ^ 2)⁻¹) := by
    have : (fun k : ℕ => (z / q ^ 2) ^ (2 * k + 1) * q ^ (2 * k + 1 + 2 * ((2 * k + 1) / 2))) =
        fun k => z / q * (z ^ 2) ^ k := funext fun k => term_odd q z hq k
    rw [this]; exact hg.mul_left _
  have h1 : (1 : ℂ) - z ^ 2 ≠ 0 := by
    intro h
    have : z ^ 2 = 1 := by linear_combination -h
    have : ‖z ^ 2‖ = 1 := by rw [this, norm_one]
    linarith
  have e : (1 - z ^ 2)⁻¹ + z / q * (1 - z ^ 2)⁻¹ = (1 + q⁻¹ * z) / (1 - z ^ 2) := by
    field_simp
  rw [← e]
  exact HasSum.even_add_odd (f := fun j : ℕ => (z / q ^ 2) ^ j * q ^ (j + 2 * (j / 2))) he ho

theorem hasSum_series : ∀ (q : ℕ), 2 ≤ q → ∀ z : ℂ, ‖z‖ < 1 →
    HasSum (fun j : ℕ => (z / (q : ℂ) ^ 2) ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))))) (cSU q z) := by
  intro q hq z hz
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hA := hasSum_weighted (q : ℂ) z hq0 hz
  set w : ℂ := z / (q : ℂ) ^ 2 with hw
  set S : ℂ := (1 + (q : ℂ)⁻¹ * z) / (1 - z ^ 2) with hS
  set a : ℕ → ℂ := fun j => w ^ j * (q : ℂ) ^ (j + 2 * (j / 2)) with ha
  set b : ℕ → ℂ := fun j => if j = 0 then 0 else w * a (j - 1) with hb
  have hB : HasSum b (w * S) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    have e : (fun n => b (n + 1)) = fun n => w * a n := by
      funext n; simp [hb]
    rw [e]
    simpa [hb] using hA.mul_left w
  have hfun : (fun j : ℕ => w ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))))) =
      fun j => a j - b j := by
    funext j
    rcases j with _ | n
    · simp [ha, hb]
    · simp only [ha, hb, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      rw [pow_succ]; ring
  rw [hfun]
  have h1 : (1 : ℂ) - z ^ 2 ≠ 0 := by
    intro h
    have : z ^ 2 = 1 := by linear_combination -h
    have : ‖z ^ 2‖ = 1 := by rw [this, norm_one]
    rw [norm_pow] at this
    nlinarith [norm_nonneg z]
  have e : cSU (q : ℂ) z = S - w * S := by
    rw [cSU, hS, hw]
    field_simp
  rw [e]
  exact hA.sub hB

end GlobalTheory.SURankOneSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.NuPow

theorem pow_mem_H_and_nu_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∀ n : ℕ, f ^ n ∈ P.H (n * a) (n * b) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (n * a) (n * b) σ y (f ^ n) = P.nu a b σ y f ^ n := by
  intro k _ X _ p P a b f hf n
  induction n with
  | zero =>
    refine ⟨fun x i j _ _ => ⟨1, by simp [Pair.loc]⟩, fun σ y => ?_⟩
    have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
    rw [map_one, ev_one mem_ptsIn_top] at e
    simp [Pair.nu, Pair.loc, e]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ a b _ f ih.1 hf
    have ea : ((n + 1 : ℕ) : ℤ) * a = n * a + a := by push_cast; ring
    have eb : ((n + 1 : ℕ) : ℤ) * b = n * b + b := by push_cast; ring
    rw [ea, eb, pow_succ]
    exact ⟨h1, fun σ y => by rw [h2 σ y, ih.2 σ y, pow_succ]⟩

end GlobalTheory.VolBr.NuPow
end

