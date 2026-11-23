module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulVecEqOfBasis
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.RatHerm
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2343
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantPowEqUnitMulSymmetricFunction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegRev

theorem isIntegralElem_of_forall {V K : Type} [CommRing V] [Field K] (i : V →+* K) {x : K}
    (h : ∀ W : ValuationSubring K, (∀ v, i v ∈ W) → x ∈ W) : i.IsIntegralElem x := by
  letI : Algebra V K := i.toAlgebra
  have hic : IsIntegrallyClosedIn (integralClosure V K).toSubring K :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure V K) K)
  have h1 : x ∈ (integralClosure V K).toSubring := by
    by_contra hn
    obtain ⟨W, hW, hxW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hn
    exact hxW (h W fun v => hW ((integralClosure V K).algebraMap_mem v))
  exact h1

theorem scale_of_prim {V K : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsIntegrallyClosed V] [Field K]
    (io : FractionRing V →+* K) (N N' k : ℕ) {J : Type} (c : Fin N → K) (c' : Fin N' → K) (a : K)
    (e : Fin N → FractionRing V) (th : J → FractionRing V) (i : J) (ha : a ≠ 0) (hk : 1 ≤ k)
    (hP : Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a))
    (hP' : Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a))
    (he : ∀ j, io (e j) = symTup c j) (hth1 : ∀ x, ∃ b, c' x ^ k = io (th b) ^ k)
    (hth2 : ∀ b, ∃ x, c' x ^ k = io (th b) ^ k) (hi : th i ≠ 0)
    (hdiv : ∀ b, th b / th i ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ e' : Fin N → V, (∀ j, algebraMap V (FractionRing V) (e' j) = e j / th i ^ N.factorial) ∧
      ∃ j, IsUnit (e' j) := by
  have hk0 : k ≠ 0 := by omega
  have hti : io (th i) ≠ 0 := (map_ne_zero io).2 hi
  have hW' : ∀ W : ValuationSubring K, (∀ v, (io.comp (algebraMap V (FractionRing V))) v ∈ W) →
      io (th i) / a ∈ W ∧ a / io (th i) ∈ W := by
    intro W hW
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hth2 i
      refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
      rw [div_pow, ← hx, ← div_pow]
      exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW (hP'.1 x)) k
    · obtain ⟨x₀, hx0, hx0i⟩ := hP'.2
      obtain ⟨b₁, hb1⟩ := hth1 x₀
      have hc0 : c' x₀ ≠ 0 := fun h => hx0 (by simp [h])
      have hb10 : io (th b₁) ≠ 0 := by
        intro h0
        apply hc0
        have h2 : c' x₀ ^ k = 0 := by rw [hb1, h0, zero_pow hk0]
        exact (pow_eq_zero_iff hk0).1 h2
      have h1 : a / io (th b₁) ∈ W := by
        refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
        have e0 : (a / io (th b₁)) ^ k = ((c' x₀ / a)⁻¹) ^ k := by
          rw [inv_div, div_pow, div_pow, hb1]
        rw [e0]
        exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW hx0i) k
      have h2 : io (th b₁) / io (th i) ∈ W := by
        obtain ⟨v, hv⟩ := hdiv b₁
        have h3 := hW v
        rwa [RingHom.comp_apply, hv, map_div₀] at h3
      have e1 : a / io (th i) = a / io (th b₁) * (io (th b₁) / io (th i)) := by
        field_simp
      rw [e1]
      exact mul_mem h1 h2
  have hPt : Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / io (th i)) := by
    refine ⟨fun b => isIntegralElem_of_forall _ fun W hW => ?_, ?_⟩
    · have e1 : c b / io (th i) = c b / a * (a / io (th i)) := by field_simp
      show c b / io (th i) ∈ W
      rw [e1]
      exact mul_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW (hP.1 b)) (hW' W hW).2
    · obtain ⟨b₀, hb0, hb0i⟩ := hP.2
      have hc0 : c b₀ ≠ 0 := fun h => hb0 (by simp [h])
      refine ⟨b₀, div_ne_zero hc0 hti, isIntegralElem_of_forall _ fun W hW => ?_⟩
      have e1 : (c b₀ / io (th i))⁻¹ = io (th i) / a * (c b₀ / a)⁻¹ := by field_simp
      show (c b₀ / io (th i))⁻¹ ∈ W
      rw [e1]
      exact mul_mem (hW' W hW).1 (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW hb0i)
  have hsym : ∀ j, io (e j / th i ^ N.factorial) = symTup (fun b => c b / io (th i)) j := by
    intro j
    rw [map_div₀, map_pow, he]
    have e2 : (fun b => c b / io (th i)) = fun b => (io (th i))⁻¹ * c b := by
      funext b
      rw [div_eq_inv_mul]
    rw [e2, GlobalTheory.UMin.PrimCmp.symTup_mul, inv_pow, inv_mul_eq_div]
  exact _root_.GlobalTheory.UMin.symTup_unit_of_prim V K io N (fun b => c b / io (th i)) (fun j => e j / th i ^ N.factorial) hPt hsym

end GlobalTheory.SiegRev

theorem GlobalTheory.SiegTh.sameScale_theta_symE : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (e : Fin (N + 1) → Ω), Geo.Tor.IsNormalScheme M.Z → M.HasDiv S.th → SymE ρ m e → SameScale M S.th e (N + 1).factorial := by
  intro g n hg hn hno F W hW P rig m N f hTh o Ω _ _ _ _ β S ρ u hSys M e hNorm hDiv hSym z i hi
  obtain ⟨-, -, -, hmo, hm3, hmu, hN, -, -⟩ := hTh
  obtain ⟨-, -, hSg, -, -⟩ := hSys
  haveI : IsNoetherianRing o := by
    haveI := ArithBase.ded (o := o) (Ω := Ω)
    infer_instance
  haveI : CharZero Ω := ArithBase.char (o := o)
  haveI : IsNoetherianRing (M.O z) := RatModel.isNoetherianRing_O M z
  haveI : IsIntegrallyClosed (M.O z) := RatModel.isIntegrallyClosed_O hNorm z
  haveI : CharZero (M.O z) := ⟨fun a b h => by
    have := congrArg Subtype.val h
    simpa using this⟩
  have hmo' : IsUnit (m : o) := by simpa using hmu.map β
  have hNe : N + 1 = m ^ (4 * S.g) := by rw [hN, hSg]
  have hk : 1 ≤ (S.r * S.N) ^ 2 := Nat.one_le_iff_ne_zero.2
    (pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)))
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
      ∀ φ : M.O z →+* V, Function.Injective φ →
      ∃ emb : Ω →+* FractionRing V,
        (∀ r : M.O z, emb (algebraMap (M.O z) Ω r) = algebraMap V (FractionRing V) (φ r)) ∧
        ∃ e' : Fin (N + 1) → V,
          (∀ j, algebraMap V (FractionRing V) (e' j) = emb (e j / S.th i ^ (N + 1).factorial)) ∧
          ∃ j, IsUnit (e' j) := by
    intro V _ _ _ hV φ hφ
    haveI : IsDiscreteValuationRing V := hV.1
    have hg : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
      (IsFractionRing.injective V (FractionRing V)).comp hφ
    let emb : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O z) hg
    have hemb : ∀ r : M.O z, emb (algebraMap (M.O z) Ω r) = algebraMap V (FractionRing V) (φ r) := fun r =>
      IsFractionRing.lift_algebraMap (A := M.O z) hg r
    have hmemO : ∀ x ∈ M.O z, emb x ∈ Set.range (algebraMap V (FractionRing V)) := fun x hx =>
      ⟨φ ⟨x, hx⟩, (hemb ⟨x, hx⟩).symm⟩
    have ho : ∀ a : o, emb (algebraMap o Ω a) ∈ Set.range (algebraMap V (FractionRing V)) := fun a =>
      hmemO _ ((M.O z).algebraMap_mem a)
    obtain ⟨K, _, io, N', c, c', a, ha, hP, hP', he, h1, h2⟩ :=
      _root_.GlobalTheory.SiegTh.TraitScale.exists_scale o Ω S ρ m (N + 1) e hmo hm3 hmo' hNe hSym V hV emb ho
    have hr : ∀ b, emb (S.th b) / emb (S.th i) ∈ Set.range (algebraMap V (FractionRing V)) := fun b => by
      rw [← map_div₀]
      exact hmemO _ (hi.2 b)
    obtain ⟨e', he', j, hj⟩ := GlobalTheory.SiegRev.scale_of_prim io (N + 1) N' ((S.r * S.N) ^ 2) c c' a
      (fun j => emb (e j)) (fun b => emb (S.th b)) i ha hk hP hP' he h1 h2 ((map_ne_zero emb).2 hi.1) hr
    refine ⟨emb, hemb, e', fun j => ?_, j, hj⟩
    rw [he', map_div₀, map_pow]
  have hmem : ∀ j, e j / S.th i ^ (N + 1).factorial ∈ M.O z := by
    intro j
    obtain ⟨x, s, hs, hx⟩ := IsFractionRing.div_surjective (A := M.O z) (e j / S.th i ^ (N + 1).factorial)
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hdvd : s ∣ x := _root_.GlobalTheory.DvrDiv.dvd_of_forall_cDvr (M.O z) x s hs0 (fun V _ _ _ hV φ hφ => by
      obtain ⟨emb, hemb, e', he', -⟩ := key V hV φ hφ
      have hv := he' j
      rw [← hx, map_div₀, hemb, hemb] at hv
      have hs' : algebraMap V (FractionRing V) (φ s) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 ((map_ne_zero_iff φ hφ).2 hs0)
      refine ⟨e' j, IsFractionRing.injective V (FractionRing V) ?_⟩
      rw [map_mul, hv, mul_div_cancel₀ _ hs'])
    obtain ⟨c, hc⟩ := hdvd
    have hs1 : algebraMap (M.O z) Ω s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    rw [← hx, hc, map_mul, mul_div_cancel_left₀ _ hs1]
    exact c.2
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (M.O z)
  haveI := hloc
  obtain ⟨emb, hemb, e', he', j, hj⟩ := key V hV φ hφ
  have hj' : e' j = φ ⟨_, hmem j⟩ := IsFractionRing.injective V (FractionRing V) (by rw [he', ← hemb]; rfl)
  have hu : IsUnit (⟨e j / S.th i ^ (N + 1).factorial, hmem j⟩ : M.O z) := isUnit_of_map_unit φ _ (hj' ▸ hj)
  obtain ⟨h0, hinv⟩ := (RatModel.isUnit_O_iff _).1 hu
  have h0' : e j / S.th i ^ (N + 1).factorial ≠ 0 := h0
  have hinv' : (e j / S.th i ^ (N + 1).factorial)⁻¹ ∈ M.O z := hinv
  have hthD : S.th i ^ (N + 1).factorial ≠ 0 := pow_ne_zero _ hi.1
  have hej : e j ≠ 0 := fun h => h0' (by simp [h])
  refine ⟨j, ⟨hej, fun k => ?_⟩, ?_, hmem j⟩
  · have e3 : e k / e j = e k / S.th i ^ (N + 1).factorial * (e j / S.th i ^ (N + 1).factorial)⁻¹ := by
      field_simp
    rw [e3]
    exact mul_mem (hmem k) hinv'
  · simpa only [inv_div] using hinv'

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEV0EqICPqRows
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BigTop.Fun

open Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Cx.CxData
open scoped InnerProductSpace Matrix

theorem iC_cpt_eq_theta_toR {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool) (t : Bs.Tup) (z : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding z) = X.Θ t (X.jR t (cr.toR X.zs b t z)) := by
  conv_rhs => rw [pi_eq_sum_univ z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, iC, lin, Fintype.linearCombination_apply, cpt]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 4
  ext j
  simp [Pi.single_apply, eq_comm]

theorem theta_jR_eq_zero_of_perp {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    (cv : CrdV A) (hJ : X.JIsoR cv) (hZ : X.RatZ) (t : Bs.Tup) (x : A.FR t) (hx : ∀ w ∈ X.Z t, cv.hR t w x = 0) :
    X.Θ t (X.jR t x) = 0 := by
  have hperp : ∀ m ∈ Submodule.span ℂ ((X.jR t) '' (X.Z t : Set (A.FR t))), ⟪m, X.jR t x⟫_ℂ = 0 := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨w, hw, rfl⟩ := hm
      rw [hJ t w x, hx w hw, map_zero]
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  refine ext_inner_left ℂ fun e => ?_
  rw [inner_zero_right, ← LinearMap.adjoint_inner_left]
  apply hperp
  rw [hZ.1 t]
  exact LinearMap.mem_range_self _ _

theorem sub_zE_Pq_mem_U {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (hs : Function.Surjective (B.Pq ℓ Z).mulVec)
    (y : Fin (B.nV ℓ) → K) : y - (B.zE ℓ Z).mulVec ((B.Pq ℓ Z).mulVec y) ∈ B.U ℓ Z := by
  set E := B.zE ℓ Z with hE
  set H := B.HV ℓ with hH
  have hdet : IsUnit (Eᴴ * H * E).det := by
    by_contra hu
    have h0 : B.Pq ℓ Z = 0 := by
      show (Eᴴ * H * E)⁻¹ * (Eᴴ * H) = 0
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hu, Matrix.zero_mul]
    apply hu
    have hd : B.dZ ℓ Z = 0 := by
      by_contra hne
      obtain ⟨i⟩ : Nonempty (Fin (B.dZ ℓ Z)) := ⟨⟨0, Nat.pos_of_ne_zero hne⟩⟩
      obtain ⟨x, hx⟩ := hs (Pi.single i 1)
      rw [h0, Matrix.zero_mulVec] at hx
      have := congrFun hx i
      simp at this
    have : IsEmpty (Fin (B.dZ ℓ Z)) := ⟨fun i => by have := i.2; omega⟩
    rw [Matrix.det_isEmpty]
    exact isUnit_one
  have hO := (Formalism.DivisionValues.exponent_index_lattice.isOrthProj_formula H E hdet).2
  intro z hz
  obtain ⟨c, rfl⟩ : ∃ c, E.mulVec c = z := by
    have h := (Formalism.L2.DIV.subspace_image_spec K _ (B.Z0 ℓ Z)).2
    have : z ∈ LinearMap.range (subE (B.Z0 ℓ Z)).mulVecLin := by rw [h]; exact hz
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc⟩
  rw [Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have : Eᴴ *ᵥ (H *ᵥ (y - E *ᵥ (B.Pq ℓ Z *ᵥ y))) = (Eᴴ * H * (1 - E * B.Pq ℓ Z)) *ᵥ y := by
    simp only [Matrix.mulVec_sub, Matrix.mul_sub, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_one, Matrix.mul_assoc]
  rw [this]
  show star c ⬝ᵥ (Eᴴ * H * (1 - E * ((Eᴴ * H * E)⁻¹ * (Eᴴ * H)))) *ᵥ y = 0
  rw [hO, Matrix.zero_mulVec, dotProduct_zero]

theorem csum_goodPart_perp_eq_zero {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (s : ℕ) (hB : B.Ok s) (v0 : InfinitePlace K) (hv : Formalism.DivisionValues.IsConjAt v0) (ℓ : Lvl K G)
    (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms) (hZ : ∀ g, Z ≤ Z.comap (B.r g))
    (u : Fin (B.nV ℓ) → K) (hu : u ∈ B.U ℓ Z) (w : B.S.Forms) (hw : w ∈ Z) :
    B.S.csum (w : B.S.Cl → B.S.V) ((B.S.basis.equivFun.symm ((B.vE ℓ).mulVec u) : B.S.Forms) : B.S.Cl → B.S.V) = 0 := by
  classical
  have hpe := good_at_spec K v0 hv G ℓ.X hX ℓ.P ℓ.ψ
  obtain ⟨hO, hEP⟩ := orthogonal_projection_spec K v0 hv B.S (hB.hpos v0) G B.r hB.act _ hpe.idem hpe.selfAdj
  have hadj := group_action_matrix_adjoint K B.S G B.r hB.act (goodAt ℓ.X ℓ.P ℓ.ψ)
  rw [hpe.selfAdj] at hadj
  have hE : B.vE ℓ = B.S.cutE B.r (goodAt ℓ.X ℓ.P ℓ.ψ) := rfl
  set Gm := B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ) with hGm
  set E := B.vE ℓ with hEdef
  set x := B.S.basis.equivFun w with hx
  have hw' : (w : B.S.Cl → B.S.V) = B.S.I x := by simp [CSD.I, x]
  have hv' : ((B.S.basis.equivFun.symm (E.mulVec u) : B.S.Forms) : B.S.Cl → B.S.V) = B.S.I (E.mulVec u) := rfl
  rw [hw', hv', CSD.csum_sum, ← Formalism.DivisionValues.RationalHermitianForm.hform_apply]
  have hGE : Gm *ᵥ (E *ᵥ u) = E *ᵥ u := by
    have hO1 : B.S.cutPr B.r (goodAt ℓ.X ℓ.P ℓ.ψ) * E = 1 := hO.1
    rw [← hEP, Matrix.mulVec_mulVec, ← hE, Matrix.mul_assoc, hO1, Matrix.mul_one]
  rw [← hGE]
  have hmove : Formalism.DivisionValues.hform B.S.H x (Gm *ᵥ (E *ᵥ u)) = Formalism.DivisionValues.hform B.S.H (Gm *ᵥ x) (E *ᵥ u) := by
    rw [Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Matrix.mulVec_mulVec, ← hadj,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  set z' := B.S.cutPr B.r (goodAt ℓ.X ℓ.P ℓ.ψ) *ᵥ x with hz'def
  have hGx : Gm *ᵥ x = E *ᵥ z' := by rw [← hEP, ← Matrix.mulVec_mulVec, hE]
  have hz' : z' ∈ B.Z0 ℓ Z := by
    show (E.mulVecLin z') ∈ B.coord Z
    rw [Matrix.mulVecLin_apply, ← hGx]
    refine ⟨B.S.gaOp B.r (goodAt ℓ.X ℓ.P ℓ.ψ) w, ?_, ?_⟩
    · show (B.S.gaOp B.r (goodAt ℓ.X ℓ.P ℓ.ψ) w) ∈ Z
      simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply]
      exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hZ t hw)
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hGm,
        CSD.gaMat, Matrix.sum_mulVec, Matrix.smul_mulVec]
        refine Finset.sum_congr rfl fun t _ => ?_
        congr 1
        show B.S.basis.equivFun (B.r t w) = (LinearMap.toMatrix B.S.basis B.S.basis (B.r t)) *ᵥ (B.S.basis.equivFun w)
        rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  rw [hmove, hGx, ← Formalism.L2.DIV.hform_cut]
  have hP : (Nat.card ℓ.P : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hH : Eᴴ * B.S.H * E = (Nat.card ℓ.P : K) • B.HV ℓ := by
    simp only [hEdef, BlockDat.HV, BlockDat.vE, CSD.goodPartHermitianForm, CSD.cutH, CSD.V0E, smul_smul, mul_inv_cancel₀ hP, one_smul]
  rw [hH, Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Matrix.smul_mulVec, dotProduct_smul, ← Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot,
    hu z' hz', smul_zero]


end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelPointLatticePeriodsTraits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Periods

theorem one_lattice {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (D : DegData R (maximalIdeal R)) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W)
    (m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X)) (P : ∀ T : Trait F, (R →+* T.V) → Prop)
    (h : ∀ T ψ, P T ψ → ∃ ρT : D.toPre.X ≃+ (Fin 8 → T.D.toPre.X),
      (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧
      ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y))) :
    ∃ (Λ : Type) (_ : AddCommGroup Λ) (p : Λ → R) (c : ℕ), 1 ≤ c ∧ ∀ T ψ, P T ψ →
      ∃ e : Λ ≃+ T.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = c * T.β (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  have hc : 0 < W 0 0 := by
    have := hW.1.diag_pos (i := 0)
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply] at this
    have h2 : (0 : ℤ) < W 0 0 + W 0 0 := by exact_mod_cast this
    omega
  by_cases hex : ∃ T ψ, P T ψ
  swap
  · push_neg at hex
    exact ⟨PUnit, inferInstance, fun _ => 0, 1, le_rfl, fun T ψ hP => absurd hP (hex T ψ)⟩
  obtain ⟨T₀, ψ₀, hP₀⟩ := hex
  obtain ⟨e₀, -, he₀⟩ := h T₀ ψ₀ hP₀
  have hcoord : ∀ z, ∃ r, PsiCoord D.toPre (e₀.symm (Pi.single 0 z)) r := fun z =>
    (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D.toPre _).2 (GlobalTheory.PeriodFormCompare.psiIn_top D _)
  choose p hp using hcoord
  refine ⟨T₀.D.toPre.X, inferInstance, p, (W 0 0).toNat, by omega, fun T ψ hP => ?_⟩
  obtain ⟨ρT, hρ, hm⟩ := h T ψ hP
  obtain ⟨π, hπs, hπ⟩ := exists_diag_of_matRel W hW D.toPre.X T₀.D.toPre.X T.D.toPre.X m e₀ ρT.toAddMonoidHom
    ρT.surjective he₀ hm
  have hsingle : ∀ z, ρT (e₀.symm (Pi.single 0 z)) = Pi.single 0 (π z) := by
    intro z
    funext u
    have := hπ (e₀.symm (Pi.single 0 z)) u
    simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply] at this
    rw [this]
    by_cases hu : u = 0
    · subst hu; simp
    · simp [Pi.single_apply, hu]
  have hinj : Function.Injective π := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    have h1 : ρT (e₀.symm (Pi.single 0 z)) = 0 := by rw [hsingle, hz, Pi.single_zero]
    have h2 : e₀.symm (Pi.single 0 z) = 0 := by simpa using h1
    have h3 : (Pi.single 0 z : Fin 8 → T₀.D.toPre.X) = 0 := by simpa using h2
    simpa using congrFun h3 0
  refine ⟨AddEquiv.ofBijective π ⟨hinj, hπs⟩, fun z => ?_⟩
  obtain ⟨h0, ha⟩ := hρ _ _ (hp z)
  rw [hsingle] at h0 ha
  have hq : qW W T.β (Pi.single 0 (π z)) = W 0 0 * T.β (π z) (π z) := by
    unfold qW
    rw [Finset.sum_eq_single 0 (fun u _ hu => by simp [Pi.single_eq_of_ne hu]) (by simp)]
    rw [Finset.sum_eq_single 0 (fun v _ hv => by simp [Pi.single_eq_of_ne hv]) (by simp)]
    simp
  refine ⟨(qW W T.β (Pi.single 0 (π z))).toNat, ?_, ha⟩
  rw [Int.toNat_of_nonneg h0, hq, Int.toNat_of_nonneg hc.le]
  rfl

end GlobalTheory.Poinc.Periods

theorem GlobalTheory.Poinc.Periods.trait_iso : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (f : Fin 8 → Fin 8 → (FinalForm.G ⟶ FinalForm.G)), (∀ a b, MatOn FinalForm pr a b (f a b)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (ξ : Sp R ⟶ M.Z) [IsCommMonObj ((Over.pullback ξ).obj FinalForm.G)] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A ((Over.pullback ξ).obj FinalForm.G)), LBIso U.LG.L (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom ξ)) → (∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus FinalForm.G)) → ∀ (m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X)), (∀ a b, EndChar U ((Over.pullback ξ).map (f a b)) (m a b)) → ∀ (T : Trait F) (ψ : R →+* T.V), IsLocalHom ψ → ThroughU M V v (𝟙 F.X) T (spMap ψ ≫ ξ) → ∃ ρT : D.toPre.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  intro g n o _ ζ F W hW o' Ω _ _ _ hA S ρ u c pr hs M U₀ EE FinalForm hO V v hv f hf R _ _ _ hB ξ _ D A U hL hP m hm T ψ hl ht
  have hVab := (_root_.GlobalTheory.Poinc.Eq8.SharpOnV.main g n o ζ F W o' Ω S ρ u c pr hs M U₀ EE FinalForm hO V v hv).1
  have hBV : GlobalTheory.Mum.Base T.V := ⟨⟨inferInstance, inferInstance, inferInstance, T.complete⟩, inferInstance⟩
  have hgen : ∀ w, (jK T.V ≫ spMap ψ ≫ ξ) w ∈ abLocus FinalForm.G := by
    obtain ⟨ξ₀, hξ₀, -⟩ := ht
    intro w
    rw [← hξ₀]
    exact hVab (ξ₀ w).2
  obtain ⟨G', _, _, D', A', U', gm, ι, hG', hgm, hLB, hC, hE⟩ :=
    _root_.GlobalTheory.Poinc.Eq8.PullComplete.main M.Z FinalForm.G FinalForm.semi FinalForm.L.L R hB ξ D A U hL hP T.V hBV ψ hl hgen
  refine _root_.GlobalTheory.Poinc.Eq8.PeriodsEighth.main g n o ζ F W hW o' Ω S ρ u c pr hs M U₀ EE FinalForm hO V v hv f hf R ξ D.toPre m
    T ψ ht G' D' A' U' gm ι hG' hgm hLB hC fun a b => ?_
  obtain ⟨f', hf'm, hf'c, hf'e⟩ := hE (f a b) (hf a b).1
  exact ⟨f', hf'm, hf'c, fun m' hm' => hf'e _ m' (hm a b) hm'⟩

theorem GlobalTheory.Poinc.Periods.main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ x : M.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (p : Λ → R) (c : ℕ), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ 1 ≤ c ∧ ∀ (T : Trait F) (ψ : R →+* T.V), IsLocalHom ψ → ThroughU M V v (𝟙 F.X) T (spMap (ψ.comp j) ≫ M.Z.fromSpecStalk x) → ∃ e : Λ ≃+ T.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = c * T.β (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  intro g n o _ ζ F W hW o' Ω _ _ _ hA S ρ u hu M U₀ EE FinalForm hO V v hv x
  obtain ⟨c, pr, hs⟩ := (sharpOver_iff F W ρ.P u).1 hu
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI : IsIntegrallyClosed (M.Z.presheaf.stalk x) := (hO.normal x).2
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have fg : (maximalIdeal (M.Z.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x) with hR
  set φ := algebraMap (M.Z.presheaf.stalk x) R with hφ
  have hcpl : IsAdicComplete (maximalIdeal R) R := by
    rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  have hinj : Function.Injective φ := AdicCompletion.of_injective _ _
  haveI : CharZero R := (RingHom.charZero_iff hinj).1 inferInstance
  set ξ : Sp R ⟶ M.Z := spMap φ ≫ M.Z.fromSpecStalk x with hξ
  have hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty := by
    let w : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    let p : Sp (M.Z.presheaf.stalk x) := spMap φ w
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap φ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot φ).1 hinj
    have hgen : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact genericPoint_specializes x
    obtain ⟨q, hq⟩ := hgen
    have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
      show p.asIdeal ≤ q.asIdeal
      rw [hp]
      exact bot_le)
    have hsp : ξ w ⤳ genericPoint M.Z := by
      have := hpq.map (M.Z.fromSpecStalk x).continuous
      rw [hq] at this
      exact this
    refine ⟨w, ?_⟩
    show ξ w ∈ abLocus FinalForm.G
    rw [FinalForm.ab]
    exact le_bot_iff.1 ((S.TT_anti M hsp).trans (ThetaSys.TT_genericPoint S M).le)
  haveI : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj
  obtain ⟨D, A, U, hL, hP⟩ := FinalForm.unif R hRn hRi hcpl ξ hne
  have hB : GlobalTheory.Mum.Base R := ⟨⟨hRn, hRd, hRi, hcpl⟩, inferInstance⟩
  have hGs : IsSemiAbelian ((Over.pullback ξ).obj FinalForm.G) := IsSemiAbelian.pullback _ FinalForm.G FinalForm.semi
  obtain ⟨hsb, hpr, huniq, hlb⟩ := hs
  choose f hf using matOn_exists o' Ω S ρ M U₀ EE FinalForm hO.ne c.A pr hpr huniq
  have hfm : ∀ a b, IsMonHom ((Over.pullback ξ).map (f a b)) := fun a b => by
    have := (hf a b).1
    infer_instance
  choose m hmc using fun a b => endChar_exists_of_isMonHom R hB _ hGs D A U _ (hfm a b)
  obtain ⟨Λ, _, p, c', hc', hall⟩ := GlobalTheory.Poinc.Periods.one_lattice D W hW m
    (fun T ψ => IsLocalHom ψ ∧ ThroughU M V v (𝟙 F.X) T (spMap (ψ.comp φ) ≫ M.Z.fromSpecStalk x))
    (fun T ψ hT => by
      obtain ⟨hl, ht⟩ := hT
      have e : spMap (ψ.comp φ) ≫ M.Z.fromSpecStalk x = spMap ψ ≫ ξ := by
        rw [hξ, ← Category.assoc]
        congr 1
        exact Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)
      rw [e] at ht
      exact GlobalTheory.Poinc.Periods.trait_iso g n o ζ F W hW o' Ω S ρ u c pr ⟨hsb, hpr, huniq, hlb⟩ M U₀ EE FinalForm hO V v hv f hf R hB ξ
        D A U hL hP m hmc T ψ hl ht)
  exact ⟨R, inferInstance, hRd, hloc, φ, Λ, inferInstance, p, c', hB, isCpl_self _, hc', fun T ψ hl ht => hall T ψ ⟨hl, ht⟩⟩
end
end

