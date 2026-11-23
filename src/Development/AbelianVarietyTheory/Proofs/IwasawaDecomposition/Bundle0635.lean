module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
public import Formalism.DegreeFormula.PointDegree.PowSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0540
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLinearAlgebraHodgeSequenceExact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0531
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0538
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagMapChernRootsX
section
noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric
open Classical

namespace GlobalTheory.Schubert.RelKill

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem esymm_cons_succ {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

theorem coeff_prod_one_add {R : Type*} [CommSemiring R] (s : Multiset R) (n : ℕ) :
    ((s.map fun a => (1 + Polynomial.C a * Polynomial.X : Polynomial R)).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
      Polynomial.coeff_C_mul]
    cases n with
    | zero => simp [ih, Multiset.esymm]
    | succ n => rw [Polynomial.coeff_X_mul, ih, ih, esymm_cons_succ]

theorem esymm_add {R : Type*} [CommSemiring R] (s t : Multiset R) (n : ℕ) :
    (s + t).esymm n = ∑ i ∈ Finset.range (n + 1), s.esymm i * t.esymm (n - i) := by
  rw [← coeff_prod_one_add, Multiset.map_add (f := _), Multiset.prod_add, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_add]

theorem univ_map_eq_range {R : Type*} [Zero R] (m : ℕ) (f : Fin m → R) :
    (Finset.univ : Finset (Fin m)).val.map f =
      (Multiset.range m).map (fun i => if h : i < m then f ⟨i, h⟩ else 0) := by
  have h1 : Multiset.range m = (Finset.univ : Finset (Fin m)).val.map Fin.val := by
    rw [Fin.univ_val_map, List.ofFn_eq_map, List.map_coe_finRange_eq_range]; rfl
  rw [h1, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp [i.2]

variable {H : Host E} (Dw : Datum H)

def rootSeq (τ : GlobalTheory.AllWt.Psi H) (i : ℕ) : MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  if h : i < Dw.p + Dw.q then X (τ, ⟨i, h⟩) else 0

theorem flagMap_chernRoots_X (x : E →+* ℂ) (a : ℕ) :
    flagMap Dw (chernRoots Dw.mult (X (x, a))) =
      ((Finset.univ : Finset (Fin (Dw.mult x))).val.map (fun i => flagRoot Dw ⟨x, i⟩)).esymm a := by
  rw [chernRoots, aeval_X, flagMap, aeval_rename, aeval_esymm_eq_multiset_esymm]
  rfl

theorem roots_mem (τ : GlobalTheory.AllWt.Psi H) :
    (Finset.univ : Finset (Fin (Dw.mult τ.1))).val.map (fun i => flagRoot Dw ⟨τ.1, i⟩) =
      (Multiset.range Dw.p).map (rootSeq Dw τ) := by
  rw [univ_map_eq_range]
  have hm := GlobalTheory.PointChern.mult_of_mem Dw τ.2
  rw [show Multiset.range (Dw.mult τ.1) = Multiset.range Dw.p by rw [hm]]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  have hi' : i < Dw.mult τ.1 := by omega
  have hi2 : i < Dw.p + Dw.q := by omega
  rw [dif_pos hi', rootSeq, dif_pos hi2, flagRoot, dif_pos τ.2]

theorem range_reflect (q : ℕ) : (Multiset.range q).map (fun i => q - 1 - i) = Multiset.range q := by
  have hinj : ∀ x ∈ Multiset.range q, ∀ y ∈ Multiset.range q, q - 1 - x = q - 1 - y → x = y := by
    intro x hx y hy h; rw [Multiset.mem_range] at hx hy; omega
  refine (Multiset.Nodup.ext ((Multiset.nodup_range q).map_on hinj) (Multiset.nodup_range q)).2 fun a => ?_
  simp only [Multiset.mem_map, Multiset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro ha; exact ⟨q - 1 - a, by omega, by omega⟩

theorem roots_conj (τ : GlobalTheory.AllWt.Psi H) :
    (Finset.univ : Finset (Fin (Dw.mult (conjEmb τ.1)))).val.map
        (fun i => flagRoot Dw ⟨conjEmb τ.1, i⟩) =
      ((Multiset.range Dw.q).map (fun i => rootSeq Dw τ (Dw.p + i))).map Neg.neg := by
  rw [univ_map_eq_range]
  have hn := GlobalTheory.AllWt.conj_not_mem τ
  have hm := GlobalTheory.PointChern.mult_of_not_mem Dw hn
  rw [show Multiset.range (Dw.mult (conjEmb τ.1)) = Multiset.range Dw.q by rw [hm]]
  conv_rhs => rw [← range_reflect Dw.q, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  have hi' : i < Dw.mult (conjEmb τ.1) := by omega
  have hi2 : Dw.p + (Dw.q - 1 - i) < Dw.p + Dw.q := by omega
  have h' : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0 := by
    rw [GlobalTheory.AllWt.conjEmb_conjEmb]; exact τ.2
  have e : (⟨conjEmb (conjEmb τ.1), h'⟩ : GlobalTheory.AllWt.Psi H) = τ :=
    Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
  simp only [dif_pos hi', flagRoot, dif_neg hn, Function.comp_apply, rootSeq, dif_pos hi2, e]

theorem rename_esymm (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) :
    rename (fun i : Fin (Dw.p + Dw.q) => (τ, i)) (esymm (Fin (Dw.p + Dw.q)) ℝ k) =
      ((Multiset.range Dw.p).map (rootSeq Dw τ) +
        (Multiset.range Dw.q).map (fun i => rootSeq Dw τ (Dw.p + i))).esymm k := by
  rw [← aeval_X_left_apply (rename _ _), aeval_rename, aeval_esymm_eq_multiset_esymm, univ_map_eq_range, Multiset.range_add, Multiset.map_add (f := _),
    Multiset.map_map]
  rfl

theorem flagMap_relPoly (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) :
    flagMap Dw (chernRoots Dw.mult (GlobalTheory.PointChern.relPoly τ k)) =
      rename (fun i : Fin (Dw.p + Dw.q) => (τ, i)) (esymm (Fin (Dw.p + Dw.q)) ℝ k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rename_esymm, esymm_add, GlobalTheory.PointChern.relPoly, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_mul, map_mul, map_mul, flagMap_chernRoots_X, flagMap_chernRoots_X, roots_mem, roots_conj,
    Multiset.esymm_neg]
  have hC : flagMap Dw (chernRoots Dw.mult (C ((-1 : ℝ) ^ (k - a)))) = (-1) ^ (k - a) := by
    simp [flagMap, chernRoots]
  rw [hC]
  have h1 : ((-1 : MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ) ^ (k - a)) * (-1) ^ (k - a) = 1 := by
    rw [← mul_pow]; simp
  linear_combination (((Multiset.range Dw.p).map (rootSeq Dw τ)).esymm a *
    ((Multiset.range Dw.q).map (fun i => rootSeq Dw τ (Dw.p + i))).esymm (k - a)) * h1

end GlobalTheory.Schubert.RelKill

namespace GlobalTheory.Schubert

end GlobalTheory.Schubert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentRefinesLieFramesGraded
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.BaseRefine

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∃ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (φ : X.Fn →ₐ[F] C.Y.Fn), Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => C.gr x.1 x.2) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j hjo hj f hπ f₀ Eb A₀ hT hL
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.FlagBundle.exists_isHom_base_of_lifts E H Dw l Xo c O β Z F e C X j hjo hj f hπ hL
  have hgen : genericPt C.Y ≫ f = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X := hφ
  have hx : genericPt C.Y ≫ C.π ≫ genι Z = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X ≫ j ≫ genι Z := by
    rw [← hπ, Category.assoc, ← Category.assoc, hgen, Category.assoc]
  have hc : constF e C.Y = (φ : X.Fn →+* C.Y.Fn).comp (constF e X) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hst₀ : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f₀ inferInstance
  obtain ⟨⟨M, hM, -⟩, hMu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f₀ C.Y.Fn (constF e C.Y)
    (genericPt C.Y ≫ C.π ≫ genι Z) (φ : X.Fn →+* C.Y.Fn) inferInstance hst₀ hx hc).1 C.f0
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₀φ : ∀ τ, ((A₀.map φ) τ).det ≠ 0 := fun τ =>
    (Mat.det_map A₀ (φ : X.Fn →+* C.Y.Fn) τ).trans_ne ((map_ne_zero _).2 (hA₀d τ))
  set A₁ : Mat Dw.mult C.Y.Fn := M * A₀.map φ with hA₁
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := fun τ => by
    rw [hA₁, Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hMu M hM τ).ne_zero (hA₀φ τ)
  have hC : f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) := by
    rw [hA₁, mul_assoc, Mat.mul_inv hA₀φ, mul_one]; exact hM
  obtain ⟨E', hT', hG⟩ := _root_.GlobalTheory.ShFam.FlagTie.exists_tied_isGraded E H Dw l Xo c O β Z F e C A₁ hA₁d
  have hsub := _root_.GlobalTheory.LieBase.FlagPull.frames_sub E H Dw l Xo c O β Z F e C X j f hπ f₀ Eb A₀ hT φ hφ E' A₁ hT' hC
  exact ⟨E', φ, ⟨fun _ => Nat.zero_le _, hφ, hsub,
    _root_.GlobalTheory.FlagCptRad.keepsRad_of_flagCpt E H Dw l Xo c O β Z F e C X j hjo hj f hπ f₀ Eb A₀ hT hL φ hφ,
    _root_.GlobalTheory.ShFam.FieldLift.lifts_of_closed E H Dw l Xo c O β Z F e C X j hjo hj f hπ f₀ Eb A₀ hT hL φ hφ E' A₁ hT' hC hsub⟩, hG⟩

end GlobalTheory.ShFam.BaseRefine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.CarryAll

theorem carry_some : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (K : Type) [Field K] (χ : c.F →+* K) (p : Sp K ⟶ C.Y.X), p ≫ C.π ≫ genStr Z = spMap χ → ∃ g : EigFrame Z χ (p ≫ C.π ≫ genι Z), C.Carries p g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C K _ χ p hp
  let y : C.Y.X := p (IsLocalRing.closedPoint K)
  let ψ : C.Y.X.presheaf.stalk y →+* K := (Scheme.stalkClosedPointTo p).hom
  have hfac : p = spMap ψ ≫ stalkPt C.Y y := (Scheme.Spec_stalkClosedPointTo_fromSpecStalk p).symm
  obtain ⟨φ, fr, t, hT, -⟩ := C.gr_spec y
  obtain ⟨g, hg⟩ := EigFrame.exists_baseChange E H Dw l Xo c O β Z _ K φ (stalkPt C.Y y ≫ C.π ≫ genι Z) fr ψ
  have hs : stalkPt C.Y y ≫ C.π ≫ genStr Z = spMap φ := by
    obtain ⟨s', hs'⟩ : ∃ s' : c.F →+* C.Y.X.presheaf.stalk y, spMap s' = stalkPt C.Y y ≫ C.π ≫ genStr Z :=
      ⟨(Spec.preimage (stalkPt C.Y y ≫ C.π ≫ genStr Z)).hom, Spec.map_preimage _⟩
    rw [← hs']
    congr 1
    have ha : Function.Injective (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) :=
      IsFractionRing.injective _ _
    have h2 : (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField).comp s' = constF e C.Y := by
      apply GlobalTheory.ShFam.EigLoc.spMap_inj
      rw [GlobalTheory.ShFam.TieBase.spMap_trans, hs', ← GlobalTheory.ShFam.TieBase.genericPt_str e C.Y C.π C.π_str,
        GlobalTheory.ShFam.TieBase.genericPt_eq C.Y y]
      simp only [Category.assoc]
    refine RingHom.ext fun r => ha ?_
    have := DFunLike.congr_fun (h2.trans hT.2.1) r
    exact this
  have hφ : χ = ψ.comp φ := by
    apply GlobalTheory.ShFam.EigLoc.spMap_inj
    rw [GlobalTheory.ShFam.TieBase.spMap_trans, ← hs, ← hp, hfac]
    simp only [Category.assoc]
  subst hφ
  have key : ∀ q : Sp K ⟶ C.Y.X, q = spMap ψ ≫ stalkPt C.Y y →
      ∃ g : EigFrame Z (ψ.comp φ) (q ≫ C.π ≫ genι Z), C.Carries q g := by
    intro q hq
    subst hq
    refine ⟨g, y, ψ, φ, fr, t, 1, rfl, hT, rfl, rfl, fun τ i => ⟨Pi.single i 1, by simp, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩⟩
    have e' : (fun k => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ k) = g.v τ := funext fun k => (hg τ k).symm
    rw [e']
    exact isCombAtG_single Z.t _ (g.tan τ) i
  exact key p hfac

theorem carries_everywhere : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (k : U.Comp) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : (Φ.C k).Y.X ⟶ X.X), f ≫ j = (Φ.C k).π → ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ (Φ.C k).Y.X, p ≫ f = x ∧ (Φ.C k).Carries p g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ k X j hj hstr f hf K _ _ χ x hx g
  have hm : Mono j := by have := hj; infer_instance
  have hx' : (x ≫ j) ≫ genStr Z = spMap χ := by rw [Category.assoc]; exact hx
  have tr : ∀ (C : FlagCpt Z e) (p : Sp K ⟶ C.Y.X) (a b : Sp K ⟶ Z.X) (h : a = b) (g₀ : EigFrame Z χ a),
      C.Carries p g₀ → C.Carries p (h ▸ g₀) := by
    intro C p a b h g₀ hg; subst h; exact hg
  obtain ⟨p, hp⟩ := _root_.GlobalTheory.FlagCptBase.exists_pt_over_base E H Dw l Xo c O β Z F e σ N U Φ k X j hj hstr f hf (_root_.GlobalTheory.FlagFibre.carries_every E H Dw l Xo c O β Z F e σ N U Φ)
    (fun i K _ χ p h => carry_some E H Dw l Xo c O β Z F e (Φ.C i) K χ p h) K χ x hx
  have hπ : p ≫ (Φ.C k).π = x ≫ j := by rw [← hf, ← Category.assoc, hp]
  obtain ⟨g₀, hg₀⟩ := carry_some E H Dw l Xo c O β Z F e (Φ.C k) K χ p (by rw [← Category.assoc, hπ, Category.assoc]; exact hx)
  have h1 : p ≫ (Φ.C k).π ≫ genι Z = (x ≫ j) ≫ genι Z := by rw [← Category.assoc, hπ]
  obtain ⟨p', hp', hc⟩ := _root_.GlobalTheory.FlagFibre.carries_every E H Dw l Xo c O β Z F e σ N U Φ k K χ (x ≫ j) hx' (h1 ▸ g₀) g p hπ (tr _ p _ _ h1 g₀ hg₀)
  obtain ⟨q, -, hqu⟩ := Φ.lifts K χ (x ≫ j) hx' g
  have e' := hqu ⟨k, p'⟩ ⟨hp', hc⟩
  refine ⟨p', ⟨(cancel_mono j).1 (by rw [Category.assoc, hf, hp']), hc⟩, fun p₂ ⟨h₂, c₂⟩ => ?_⟩
  have e₂ := hqu ⟨k, p₂⟩ ⟨by rw [← hf, ← Category.assoc, h₂], c₂⟩
  exact eq_of_heq (Sigma.mk.inj_iff.1 (e₂.trans e'.symm)).2

end GlobalTheory.CarryAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatSectionIsFlat
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

section Lin

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem det_fromRows_mul (A : Matrix m m ℂ) (B : Matrix n n ℂ) (R : Matrix m (m ⊕ n) ℂ) (C : Matrix n (m ⊕ n) ℂ) :
    (Matrix.fromRows (A * R) (B * C)).det = A.det * B.det * (Matrix.fromRows R C).det := by
  rw [← Matrix.det_fromBlocks_zero₂₁ A 0 B, ← Matrix.det_mul, Matrix.fromBlocks_mul_fromRows]
  simp

theorem horVal_change {K : Matrix (m ⊕ n) m ℂ} {C : Matrix n (m ⊕ n) ℂ} {R : Matrix m (m ⊕ n) ℂ}
    {S S' : Matrix (m ⊕ n) n ℂ} (N : Matrix m m ℂ) (M : Matrix n n ℂ) (h : C * K = 0) (hS : C * S = 1)
    (hR : R * (K * N) = 1) (hS' : Mᵀ * C * S' = 1) :
    horVal K C * M.det = horVal (K * N) (Mᵀ * C) * N.det := by
  have h1 : N * R * K = 1 := by
    rw [Matrix.mul_assoc, mul_eq_one_comm, Matrix.mul_assoc]; exact hR
  have h2 : Mᵀ * C * (K * N) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, h]; simp
  have e1 := det_fromRows_mul N 1 R C
  have e2 := det_fromRows_mul 1 Mᵀ R C
  rw [Matrix.one_mul] at e1 e2
  rw [horVal_eq h h1 hS, horVal_eq h2 hR hS', e1, e2]
  simp only [Matrix.det_one, Matrix.det_transpose]
  ring

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem differentiableAt_det {A : V → Matrix m m ℂ} {b : V} (h : ∀ i j, DifferentiableAt ℂ (fun b => A b i j) b) :
    DifferentiableAt ℂ (fun b => (A b).det) b := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun s _ => (differentiableAt_const _).mul ?_
  exact (HasFDerivAt.finsetProd fun i _ => (h _ _).hasFDerivAt).differentiableAt

theorem differentiableAt_horVal {K : V → Matrix (m ⊕ n) m ℂ} {C : V → Matrix n (m ⊕ n) ℂ} {b₀ : V}
    (hK : ∀ i j, DifferentiableAt ℂ (fun b => K b i j) b₀) (hC : ∀ i j, DifferentiableAt ℂ (fun b => C b i j) b₀)
    {R : Matrix m (m ⊕ n) ℂ} (hR : R * K b₀ = 1)
    (h : ∀ᶠ b in 𝓝 b₀, C b * K b = 0 ∧ ∃ S : Matrix (m ⊕ n) n ℂ, C b * S = 1) :
    DifferentiableAt ℂ (fun b => horVal (K b) (C b)) b₀ := by
  have d1 : DifferentiableAt ℂ (fun b => (R * K b).det) b₀ := differentiableAt_det fun i j => by
    simp only [Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun k _ => (differentiableAt_const _).mul (hK _ _)
  have d2 : DifferentiableAt ℂ (fun b => (Matrix.fromRows R (C b)).det) b₀ := differentiableAt_det fun i j => by
    rcases i with i | i
    · exact differentiableAt_const _
    · exact hC i j
  have n1 : (R * K b₀).det ≠ 0 := by rw [hR]; simp
  have d3 : DifferentiableAt ℂ (fun b => (Matrix.fromRows R (C b)).det * ((R * K b).det)⁻¹) b₀ :=
    d2.fun_mul (d1.fun_inv n1)
  refine d3.congr_of_eventuallyEq ?_
  filter_upwards [h, d1.continuousAt.eventually_ne n1] with b ⟨h0, S, hS⟩ hb
  have hu : IsUnit (R * K b).det := hb.isUnit
  have e := det_fromRows_mul (R * K b)⁻¹ 1 R (C b)
  rw [Matrix.one_mul] at e
  rw [horVal_eq h0 (R := (R * K b)⁻¹ * R) (by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu]) hS, e,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Matrix.det_one]
  ring

end Lin

theorem exists_generates {F : Type} [Field F] (Y : GlobalTheory.ProjVar.Var F) (D : Y.Dv) (h : Y.H0 D ≠ ⊥)
    (h' : Y.H0 (-D) ≠ ⊥) : ∃ s, ∀ y, D.GeneratesAt y s := by
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h'
  have hst : s * t ∈ Y.H0 0 := add_neg_cancel D ▸ Y.mul_mem_riemannRochSpace_add _ _ _ _ hs ht
  let L : Y.H0 0 →ₗ[F] Y.H0 0 := (LinearMap.mulLeft F (s * t)).restrict fun g hg =>
    add_zero (0 : Y.Dv) ▸ Y.mul_mem_riemannRochSpace_add _ _ _ _ hst hg
  have hinj : Function.Injective L := fun a b e =>
    Subtype.ext (mul_left_cancel₀ (mul_ne_zero hs0 ht0) (congrArg Subtype.val e))
  letI : FiniteDimensional F (Y.H0 0) := by
    have := finite_coh_of_isProjOver Y.algebraMap_Γ (structureModule Y.X) Y.isProjOver 0
    haveI : Module.Finite F Γ(Y.X, ⊤) := .equiv ((coh.zeroUnitEquiv Y.X).restrictScalars F)
    let f : Γ(Y.X, ⊤) →ₗ[F] Y.Fn := (IsScalarTower.toAlgHom F Γ(Y.X, ⊤) Y.Fn).toLinearMap
    have hf : ∀ a, f a ∈ Y.H0 0 := fun a =>
      GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.2 fun x =>
        CartierDiv.regularAt_zero_iff.2 (regAt_fnOf trivial trivial a)
    apply Module.Finite.of_surjective (f.codRestrict _ hf)
    intro a
    obtain ⟨b, hb⟩ := exists_fnOf_eq (X := Y.X) (U := ⊤) trivial fun x _ =>
      CartierDiv.regularAt_zero_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 a.2 x)
    exact ⟨b, Subtype.ext hb⟩
  obtain ⟨u, hu⟩ := LinearMap.injective_iff_surjective.1 hinj ⟨1, GlobalTheory.ProjVar.Var.eff_iff_one_mem.1 Y.eff_zero⟩
  have hu' : s * t * u = 1 := congrArg Subtype.val hu
  refine ⟨s, fun y => ?_⟩
  obtain ⟨g, hg⟩ := D.exists_isEqn y
  have r1 := hg.regularAt_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 hs y)
  have r2 := hg.neg.regularAt_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 ht y)
  have r3 := CartierDiv.regularAt_zero_iff.1 (GlobalTheory.ProjVar.Var.mem_riemannRochSpace_iff_regularAt_everywhere.1 u.2 y)
  refine hg.generatesAt_iff.2 ((unitAt_iff (mul_ne_zero hs0 g.ne_zero)).2 ⟨r1, ?_⟩)
  have e : (s * (g : Y.Fn))⁻¹ = t * ((g⁻¹ : Y.Fnˣ) : Y.Fn) * u := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← hu', Units.val_inv_eq_inv_val]
    have := g.ne_zero
    field_simp
  exact e ▸ r2.mul r3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {σ : c.F →+* ℂ}
  {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {τ : E →+* ℂ} {x : ∀ i, Idx Dw τ → (Fu.Di i).La}
  {hm : Fin Fu.n → Matrix (Idx Dw τ) (Idx Dw τ) E}

end GlobalTheory.ShFam.Hor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodPlaceCuspidalType
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.CuspOfParam

theorem goodRow_cuspidal : ∀ (D : D7) (Rw : RowSide D), Nonempty D.nd.Loc → (∀ i σ w, D.naut.locW i σ w = Rw.locR σ w) → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.ntypes.cuspidal σ := by
  intro D Rw hLoc hW hG j hj1 hj2 σ hσ hgood
  obtain ⟨i⟩ := hLoc
  obtain ⟨π, hcsd, hralg, hsplit, -, -, -⟩ := hG j hj1 hj2 σ hσ hgood
  have hr : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    simp only [Ranks.r]
    omega
  have hiso : ∀ w, Formalism.MainNotions.N.isoLoc D.nd D.naut [(⟨D.R.r, π, 1⟩ : Part D.naut.CG)] w = D.naut.locG π w := by
    intro w
    simp [Formalism.MainNotions.N.isoLoc, Formalism.MainNotions.N.spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]
  have hpar : Formalism.MainNotions.N.HasParamW D.nd D.naut i σ [(⟨D.R.r, π, 1⟩ : Part D.naut.CG)] := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨hr, le_refl 1⟩
    · simp [Formalism.MainNotions.N.rankIso]
    · intro w hw
      rw [hiso w, hsplit w hw, hW i σ w]
  have h := D.bc_tie i σ _ hpar
    (by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact hcsd)
    (by
      intro p hp τ
      simp only [List.mem_singleton] at hp
      subst hp
      obtain ⟨hnd, hz⟩ := (D.naut.ralg_def π).1 hralg τ
      refine ⟨hnd, fun z hz' => ?_⟩
      obtain ⟨n, hn⟩ := hz z hz'
      exact ⟨n, by rw [hn]; simp⟩)
  show D.ntypes.bc σ = {(D.R.r, 1)}
  rw [h]
  simp

end GlobalTheory.HeightCounting.CuspOfParam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImIntCombinationDotProduct
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem hermForm_im_intComb_dotProduct : ∀ (g r r₀ : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (w : Fin r₀ → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ i, w i = ∑ j, c i j • l j) → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ∀ u u' : Fin r₀ → ℤ, (hermForm Hm (∑ i, u i • w i) (∑ j, u' j • w j)).im = (((∑ i, u i • c i) ⬝ᵥ M *ᵥ (∑ i, u' i • c i) : ℤ) : ℝ) := by
  intro g r r₀ Hm l w c M hw hM u u'
  have hre : ∀ v : Fin r₀ → ℤ, ∑ i, v i • w i = ∑ j, (∑ i, v i • c i) j • l j := by
    intro v
    simp only [hw, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [hre u, hre u', hermForm_im_sum]
  simp only [hM, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.ShFam.Hor.LogCh.Core
end

