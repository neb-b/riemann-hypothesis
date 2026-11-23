module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CMemDeltaCommuteLocusSubringOfIsHausdorff
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.WDelta

variable {l : ℕ} {A : Type} [CommRing A]

theorem δ_pow_succ (D : Delta l A) (z : A) (m : ℕ) :
    ∃ c, D.δ (z ^ (m + 1)) = ((m + 1 : ℕ) : A) * z ^ (l * m) * D.δ z + (l : A) * D.δ z ^ 2 * c := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨z ^ l * c + ((m + 1 : ℕ) : A) * z ^ (l * m) + (l : A) * D.δ z * c, ?_⟩
    have e1 : (z ^ (m + 1)) ^ l = z ^ (l * m) * z ^ l := by rw [← pow_mul, ← pow_add]; ring_nf
    have e2 : z ^ (l * (m + 1)) = z ^ (l * m) * z ^ l := by rw [← pow_add]; ring_nf
    rw [pow_succ z (m + 1), D.δ_mul, hc, e1, e2]
    push_cast
    ring

theorem δ_pow_pow [hl : Fact l.Prime] (D : Delta l A) (y : A) (n : ℕ) :
    D.δ (y ^ (l ^ n)) ∈ Ideal.span {(l : A)} ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := δ_pow_succ D (y ^ (l ^ n)) (l - 1)
    rw [Nat.sub_add_cancel hl.out.one_le] at hc
    rw [pow_succ l n, pow_mul, hc, pow_succ]
    have : ((l : ℕ) : A) * (y ^ l ^ n) ^ (l * (l - 1)) * D.δ (y ^ l ^ n) + (l : A) * D.δ (y ^ l ^ n) ^ 2 * c =
        D.δ (y ^ l ^ n) * ((l : A) * ((y ^ l ^ n) ^ (l * (l - 1)) + D.δ (y ^ l ^ n) * c)) := by ring
    rw [this]
    exact Ideal.mul_mem_mul ih (Ideal.mem_span_singleton.2 (dvd_mul_right _ _))

theorem eq_zero_of_mem_pow {C : Type} [CommRing C] {J : Ideal C} (h : IsHausdorff J C) {x : C}
    (hx : ∀ n, x ∈ J ^ n) : x = 0 :=
  h.haus x fun n => by rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]; exact hx n

variable (l) (a : ℕ) [hl : Fact l.Prime] [NeZero a]

theorem teich_eq_pow (n : ℕ) (x : Fq l a) :
    ∃ y : Fq l a, WittVector.teichmuller l x = WittVector.teichmuller l y ^ (l ^ n) := by
  induction n with
  | zero => exact ⟨x, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨y ^ (l ^ (a - 1)), ?_⟩
    have h1 : (y ^ (l ^ (a - 1))) ^ l = y := by
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (NeZero.pos a)]; exact Fq.pow_card (l := l) (a := a) y
    rw [hy, pow_succ' l n, pow_mul, ← map_pow (WittVector.teichmuller l) (y ^ l ^ (a - 1)) l, h1]

theorem deltaS_C_teich (x : Fq l a) :
    (deltaS l a).δ (PowerSeries.C (WittVector.teichmuller l x)) = 0 := by
  have h := (deltaS l a).φ_eq (PowerSeries.C (WittVector.teichmuller l x))
  have h2 : (deltaS l a).φ (PowerSeries.C (WittVector.teichmuller l x)) =
      PowerSeries.C (WittVector.teichmuller l x) ^ l := by
    change frobS l a _ = _
    have := sigma_pow_teich l a 1 x
    rw [pow_one, pow_one] at this
    rw [frobS_C, this, map_pow]
  rw [h2, left_eq_add] at h
  exact (mul_eq_zero.1 h).resolve_left (l_ne_zero l a)

variable {l a}

theorem C_teich_mem {C : Type} [CommRing C] (DC : Delta l C) {J : Ideal C} (hl : (l : C) ∈ J)
    (hJ : IsHausdorff J C) (σ : (Wq l a)⟦X⟧ →+* C) (x : Fq l a) :
    PowerSeries.C (WittVector.teichmuller l x) ∈ δLocus (deltaS l a) DC σ := by
  rw [mem_δLocus, deltaS_C_teich, map_zero]
  refine (eq_zero_of_mem_pow hJ fun n => ?_).symm
  obtain ⟨y, hy⟩ := teich_eq_pow l a n x
  rw [hy, map_pow, map_pow]
  exact Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem J).2 hl) n (δ_pow_pow DC _ n)

theorem approx (S : Subring (Wq l a)) (hS : ∀ x, WittVector.teichmuller l x ∈ S) (n : ℕ) (w : Wq l a) :
    ∃ s ∈ S, ∃ v, w - s = (l : Wq l a) ^ n * v := by
  induction n with
  | zero => exact ⟨0, S.zero_mem, w, by simp⟩
  | succ n ih =>
    obtain ⟨s, hs, v, hv⟩ := ih
    have h : v - WittVector.teichmuller l (v.coeff 0) ∈ Ideal.span {(l : Wq l a)} := by
      rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, sub_self]
    obtain ⟨v', hv'⟩ := Ideal.mem_span_singleton.1 h
    refine ⟨s + (l : Wq l a) ^ n * WittVector.teichmuller l (v.coeff 0),
      S.add_mem hs (S.mul_mem (S.pow_mem (natCast_mem S l) n) (hS _)), v', ?_⟩
    rw [pow_succ, mul_assoc, ← hv']
    linear_combination hv

end GlobalTheory.BSP.WDelta

namespace GlobalTheory.BSP


open GlobalTheory.BSP.WDelta in
theorem C_mem_δLocus_of_hausdorff : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Type) [CommRing C]
    (DC : Delta l C) (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ σ : (Wq l a)⟦X⟧ →+* C,
    ∀ w : Wq l a, PowerSeries.C w ∈ δLocus (deltaS l a) DC σ := by
  intro l _ a _ C _ DC J hl hJ σ w
  let S : Subring (Wq l a) := (δLocus (deltaS l a) DC σ).comap PowerSeries.C
  rw [mem_δLocus, ← sub_eq_zero]
  refine eq_zero_of_mem_pow hJ fun n => ?_
  obtain ⟨s, hs, v, hv⟩ := approx S (fun x => C_teich_mem DC hl hJ σ x) (n + 1) w
  have hs' := mem_δLocus.1 (Subring.mem_comap.1 hs)
  have hy : PowerSeries.C w - PowerSeries.C s = (l : (Wq l a)⟦X⟧) ^ (n + 1) * PowerSeries.C v := by
    rw [← map_sub, hv, map_mul, map_pow, map_natCast]
  have h1 := _root_.GlobalTheory.BSP.delta_add_sub_mem_pow l (Wq l a)⟦X⟧ (deltaS l a) (Ideal.span {(l : (Wq l a)⟦X⟧)})
    (Ideal.mem_span_singleton_self _) n (PowerSeries.C s) (PowerSeries.C w - PowerSeries.C s)
    (by rw [hy, Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _))
  rw [add_sub_cancel, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  obtain ⟨r, hr⟩ := h1
  have h2 := _root_.GlobalTheory.BSP.delta_add_sub_mem_pow l C DC J hl n (σ (PowerSeries.C s)) (σ (PowerSeries.C w - PowerSeries.C s))
    (by rw [hy, map_mul, map_pow, map_natCast]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl _))
  rw [← map_add (f := _), add_sub_cancel] at h2
  have h3 : σ ((deltaS l a).δ (PowerSeries.C w)) - σ ((deltaS l a).δ (PowerSeries.C s)) ∈ J ^ n := by
    rw [← map_sub, hr, map_mul, map_pow, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl _)
  have := (J ^ n).sub_mem h3 h2
  rw [hs'] at this
  convert this using 1
  ring

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralActsOnHeckeEigenspaceOfTypeSections
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.PendOf.EigSpanProof

section GroupAlg

variable {R : Type} [CommRing R] {G : Type} [Group G] [Fintype G]

def conjSum (w : MonoidAlgebra R G) : MonoidAlgebra R G :=
  ∑ h : G, MonoidAlgebra.of R G h * w * MonoidAlgebra.of R G h⁻¹

theorem conjSum_comm_of (w : MonoidAlgebra R G) (m : G) :
    conjSum w * MonoidAlgebra.of R G m = MonoidAlgebra.of R G m * conjSum w := by
  unfold conjSum
  rw [Finset.sum_mul, Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft m)]
  refine Finset.sum_congr rfl fun h _ => ?_
  have hm : MonoidAlgebra.of R G m⁻¹ * MonoidAlgebra.of R G m = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  simp only [Equiv.coe_mulLeft, mul_inv_rev, map_mul, mul_assoc, hm, mul_one]

theorem conjSum_mem_center (w : MonoidAlgebra R G) :
    conjSum w ∈ Subalgebra.center R (MonoidAlgebra R G) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of m => exact (conjSum_comm_of w m).symm
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem conjSum_add (x y : MonoidAlgebra R G) : conjSum (x + y) = conjSum x + conjSum y := by
  simp only [conjSum, mul_add, add_mul, Finset.sum_add_distrib]

theorem conjSum_smul (r : R) (x : MonoidAlgebra R G) : conjSum (r • x) = r • conjSum x := by
  simp only [conjSum, Finset.smul_sum, mul_smul_comm, smul_mul_assoc]

theorem conjSum_of_central (z : MonoidAlgebra R G) (hz : ∀ a, z * a = a * z) :
    conjSum z = Fintype.card G • z := by
  unfold conjSum
  have e : ∀ h : G, MonoidAlgebra.of R G h * z * MonoidAlgebra.of R G h⁻¹ = z := fun h => by
    rw [mul_assoc, hz, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  simp only [e, Finset.sum_const, Finset.card_univ]

theorem mapCoef_conjSum {S : Type} [CommRing S] (f : R →+* S) (w : MonoidAlgebra R G) :
    PairedCharacterCondition.mapCoef f (conjSum w) = conjSum (PairedCharacterCondition.mapCoef f w) := by
  show MonoidAlgebra.mapRingHom G f (conjSum w) = conjSum (MonoidAlgebra.mapRingHom G f w)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [conjSum, map_sum, map_mul, MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single, map_one]

theorem mapCoef_of {S : Type} [CommRing S] (f : R →+* S) (m : G) :
    PairedCharacterCondition.mapCoef f (MonoidAlgebra.of R G m) = MonoidAlgebra.of S G m := by
  show MonoidAlgebra.mapRingHom G f _ = _
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single, map_one]

theorem mapCoef_central {S : Type} [CommRing S] (f : R →+* S) (z : MonoidAlgebra R G)
    (hz : z ∈ Subalgebra.center R (MonoidAlgebra R G)) :
    PairedCharacterCondition.mapCoef f z ∈ Subalgebra.center S (MonoidAlgebra S G) := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of m =>
    rw [← mapCoef_of f m]
    show MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _ =
      MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _
    rw [← map_mul, ← map_mul, hz]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem mapCoef_smul {S : Type} [CommRing S] (f : R →+* S) (r : R) (x : MonoidAlgebra R G) :
    PairedCharacterCondition.mapCoef f (r • x) = f r • PairedCharacterCondition.mapCoef f x := by
  ext g
  simp [PairedCharacterCondition.mapCoef]

theorem mapCoef_add {S : Type} [CommRing S] (f : R →+* S) (x y : MonoidAlgebra R G) :
    PairedCharacterCondition.mapCoef f (x + y) = PairedCharacterCondition.mapCoef f x + PairedCharacterCondition.mapCoef f y :=
  map_add (MonoidAlgebra.mapRingHom G f) x y

end GroupAlg

section Forms

variable {D : D7}

theorem onMt_add (i : D.nd.Loc) {a b : MonoidAlgebra ℂ (G0g D.nd)}
    (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))
    (hb : b ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (a + b) =
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i) a + D.ntypes.onMt (D.nd.mu i) (D.nd.j i) b := by
  unfold NTypes.onMt
  rw [dite_eq_left ha, dite_eq_left hb, dite_eq_left (add_mem ha hb), ← map_add (f := _)]
  rfl

theorem onMt_smul (i : D.nd.Loc) (c : ℂ) {a : MonoidAlgebra ℂ (G0g D.nd)}
    (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (c • a) = c • D.ntypes.onMt (D.nd.mu i) (D.nd.j i) a := by
  unfold NTypes.onMt
  rw [dite_eq_left ha, dite_eq_left (Subalgebra.smul_mem _ ha c), ← map_smul]
  rfl

theorem onMt_typeSum (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (z : MonoidAlgebra ℂ (G0g D.nd))
    (o : Option (D.nd.X i)) :
    typeSum D i o ≤ (typeSum D i o).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) z) := by
  refine iSup₂_le fun P hP F hF => ?_
  exact Submodule.mem_comap.2 (le_biSup (D.naut.typeV i) hP (hC i P z F hF))

def ptPart (D : D7) (i : D.nd.Loc) : Submodule ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) :=
  ⨆ (o : Option (D.nd.X i)) (_ : o ≠ none), typeSum D i o

theorem onMt_ptPart (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (z : MonoidAlgebra ℂ (G0g D.nd)) :
    ptPart D i ≤ (ptPart D i).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) z) :=
  iSup₂_le fun o ho F hF => Submodule.mem_comap.2
    (Submodule.mem_iSup_of_mem o (Submodule.mem_iSup_of_mem ho (onMt_typeSum hC i z o hF)))

theorem Phi_mem {i : D.nd.Loc} (s : Sec D i) (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ w ∈ ptPart D i := by
  have hw : w ∈ ⨆ x, heckeEig (D.nd.T i) (D.nd.act i) x := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun w => s.Φ w ∈ ptPart D i) hw
    (fun x v hv => ?_) (by rw [map_zero]; exact Submodule.zero_mem _)
    (fun v v' h h' => by rw [map_add (f := _)]; exact Submodule.add_mem _ h h')
  exact Submodule.mem_iSup_of_mem (some x)
    (Submodule.mem_iSup_of_mem (Option.some_ne_none x) (s.eig x v hv))

theorem class_step (P : PairedCharacterCondition.Pend D) (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (s : Sec D i)
    (C : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (CL : MonoidAlgebra D.what₂.LL (G0g D.nd)) (hCL : ∀ a, CL * a = a * CL)
    (heq : PairedCharacterCondition.mapCoef D.what₂.embLL CL =
      PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (C : MonoidAlgebra (D.nd.O i) (G0g D.nd)))
    (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ ((P.zO i C).baseChange (KK D.nd i) w) =
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (C : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (s.Φ w) := by
  set T := D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
    (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (C : MonoidAlgebra (D.nd.O i) (G0g D.nd))) with hT
  have hw : w ∈ Submodule.span (KK D.nd i) (Set.range (D.nd.prMt i)) := by
    rw [D.nd.prMt_span i]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, rfl⟩ := hv
    obtain ⟨y', hy'⟩ := P.zL_stable i CL hCL y
    have hy2 : D.what₂.jMt _ _ y' = T (D.what₂.jMt _ _ y) := by rw [hy', heq]
    rw [← P.zO_act i C y y' hy2]
    have hind := (GlobalTheory.PendOf.PrTypeProof.typeSum_indep D i) none
    have h1 := s.split y
    have h2 := s.split y'
    have hA : s.Φ (D.nd.prMt i y') - T (s.Φ (D.nd.prMt i y)) =
        -((D.what₂.jMt _ _ y' - s.Φ (D.nd.prMt i y')) - T (D.what₂.jMt _ _ y - s.Φ (D.nd.prMt i y))) := by
      rw [map_sub T, ← hy2]; abel
    have m1 : s.Φ (D.nd.prMt i y') - T (s.Φ (D.nd.prMt i y)) ∈ typeSum D i none := by
      rw [hA]; exact Submodule.neg_mem _ (Submodule.sub_mem _ h2 (onMt_typeSum hC i _ none h1))
    have m2 : s.Φ (D.nd.prMt i y') - T (s.Φ (D.nd.prMt i y)) ∈ ptPart D i :=
      Submodule.sub_mem _ (Phi_mem s _) (onMt_ptPart hC i _ (Phi_mem s _))
    exact sub_eq_zero.1 ((Submodule.disjoint_def.1 hind) _ m1 m2)
  | zero => simp only [map_zero]
  | add v v' _ _ h h' => simp only [map_add (f := _), h, h']
  | smul a v _ h => rw [LinearMap.map_smul, s.semi, h, s.semi, LinearMap.map_smul]

end Forms

section Main

variable {D : D7}

theorem lhs_smul {i : D.nd.Loc} (s : Sec D i) (r : D.nd.O i) (f : Module.End (D.nd.O i) (D.nd.Mt i))
    (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ ((r • f).baseChange (KK D.nd i) w) = iotaO D.nd D.naut i r • s.Φ (f.baseChange (KK D.nd i) w) := by
  rw [LinearMap.baseChange_smul, LinearMap.smul_apply, ← algebraMap_smul (KK D.nd i) r, s.semi]
  rfl

theorem all_central (P : PairedCharacterCondition.Pend D) (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (s : Sec D i)
    (z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ ((P.zO i z).baseChange (KK D.nd i) w) =
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (s.Φ w) := by
  classical
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  have hQ : ∀ v : MonoidAlgebra (D.nd.O i) (G0g D.nd), ∀ w,
      s.Φ ((P.zO i ⟨conjSum v, conjSum_mem_center v⟩).baseChange (KK D.nd i) w) =
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (conjSum v)) (s.Φ w) := by
    intro v
    induction v using MonoidAlgebra.induction_on with
    | of m =>
      intro w
      refine class_step P hC i s _ (conjSum (MonoidAlgebra.of D.what₂.LL _ m))
        (fun a => ((Subalgebra.mem_center_iff.1 (conjSum_mem_center _)) a).symm) ?_ w
      show _ = PairedCharacterCondition.mapCoef _ (conjSum _)
      rw [mapCoef_conjSum, mapCoef_conjSum, mapCoef_of, mapCoef_of]
    | add x y hx hy =>
      intro w
      have e : (⟨conjSum (x + y), conjSum_mem_center _⟩ :
          ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)))) =
          ⟨conjSum x, conjSum_mem_center _⟩ + ⟨conjSum y, conjSum_mem_center _⟩ :=
        Subtype.ext (conjSum_add x y)
      rw [e, map_add (f := _), LinearMap.baseChange_add, LinearMap.add_apply, map_add (f := _), hx, hy, conjSum_add,
        mapCoef_add, onMt_add i (mapCoef_central _ _ (conjSum_mem_center _))
          (mapCoef_central _ _ (conjSum_mem_center _)), LinearMap.add_apply]
    | smul r x hx =>
      intro w
      have e : (⟨conjSum (r • x), conjSum_mem_center _⟩ :
          ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)))) =
          r • ⟨conjSum x, conjSum_mem_center _⟩ :=
        Subtype.ext (conjSum_smul r x)
      rw [e, map_smul, lhs_smul, hx, conjSum_smul, mapCoef_smul,
        onMt_smul i _ (mapCoef_central _ _ (conjSum_mem_center _)), LinearMap.smul_apply]
  have hz : ∀ a, (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) * a = a * z :=
    fun a => ((Subalgebra.mem_center_iff.1 z.2) a).symm
  set n : D.nd.O i := (Fintype.card (G0g D.nd) : D.nd.O i) with hn
  have e : (⟨conjSum (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)), conjSum_mem_center _⟩ :
      ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)))) = n • z := by
    apply Subtype.ext
    show conjSum (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) = _
    rw [conjSum_of_central _ hz, ← Nat.cast_smul_eq_nsmul (D.nd.O i)]
    rfl
  have h := hQ z w
  rw [e, map_smul, lhs_smul, hn, conjSum_of_central _ hz, ← Nat.cast_smul_eq_nsmul (D.nd.O i), mapCoef_smul,
    onMt_smul i _ (mapCoef_central _ _ z.2), LinearMap.smul_apply, map_natCast] at h
  have hne : ((Fintype.card (G0g D.nd) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  exact smul_right_injective _ hne h

theorem main : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), (∀ i, Nonempty (Sec D i)) → OnMtPreservesTypeV D → EigSpan P := by
  intro D P hS hC i z x c hzc u hu
  let s := (hS i).some
  refine s.inj ?_
  have h1 := all_central P hC i s z u
  have h2 : D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (s.Φ u) =
      iotaO D.nd D.naut i c • s.Φ u := by
    have hle : typeSum D i (some x) ≤ Module.End.eigenspace (D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)))) (iotaO D.nd D.naut i c) :=
      iSup₂_le fun PI hPI F hF => Module.End.mem_eigenspace_iff.2 (hzc PI hPI F hF)
    exact Module.End.mem_eigenspace_iff.1 (hle (s.eig x u hu))
  rw [h1, h2, ← algebraMap_smul (KK D.nd i) c u, s.semi]
  rfl

end Main

end GlobalTheory.PendOf.EigSpanProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosingNumericalInequalityTheoremB
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory

theorem closing_numerical_inequality :
    ∀ (CA C b l S η Rw Tb Vd : ℝ) (f r t m p : ℕ), 13 * max CA 0 ≤ C → 260 * f ^ 2 * t ^ 2 * (r + t) ≤ p → 1 ≤ t → 1 ≤ f → m ≤ r → 3 ≤ l → 0 ≤ S → 0 ≤ η → 0 < b → 1 < Real.log b → Rw ≤ max CA 0 * (3 * (f : ℝ) * r * (4 * b / l + 2 * S + 2 * Real.logb l (2 * b) + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1)) + f → Tb ≤ 240 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * Real.log b → Vd ≤ 4 * ((r : ℝ) + t) * t → Rw + Tb + Vd ≤ C * f * (r * (b / l + S + t + η + Real.log b) + m * b) + (p : ℝ) * Real.log b := by
  intro CA C b l S η Rw Tb Vd f r t m p hC hp ht hf hm hl hS hη hb hL hRw hTb hVd
  have hK : 0 ≤ max CA 0 := le_max_right _ _
  have hpR : (260 : ℝ) * (f : ℝ) ^ 2 * (t : ℝ) ^ 2 * ((r : ℝ) + t) ≤ (p : ℝ) := by exact_mod_cast hp
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hmR : (m : ℝ) ≤ r := by exact_mod_cast hm
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hl0 : 0 < l := by linarith

  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogl : 1 ≤ Real.log l := by
    have := Real.log_le_log (by norm_num) hl
    linarith
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith

  have hlam : Real.logb l (2 * b) ≤ 2 * Real.log b := by
    rw [Real.logb, div_le_iff₀ (by linarith), Real.log_mul (by norm_num) hb.ne']
    nlinarith
  set L := Real.log b with hLdef
  set lam := Real.logb l (2 * b) with hlamdef
  have hx : 0 ≤ b / l := div_nonneg hb.le hl0.le
  set x := b / l with hxdef
  have h4x : 4 * b / l = 4 * x := by rw [hxdef]; ring
  rw [h4x] at hRw

  have hinner : 3 * (r : ℝ) * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (m : ℝ) * (2 * b + 1)
      ≤ 13 * ((r : ℝ) * (x + S + t + η + L) + m * b) := by
    nlinarith [mul_nonneg hr0 hx, mul_nonneg hr0 hS, mul_nonneg hr0 (sub_nonneg.2 htR),
      mul_nonneg hr0 hη, mul_nonneg hr0 (sub_nonneg.2 hlam), mul_nonneg hr0 (by linarith : (0:ℝ) ≤ L),
      mul_nonneg hm0 hb.le]
  have hB : 0 ≤ (r : ℝ) * (x + S + t + η + L) + m * b := by
    have : 0 ≤ x + S + t + η + L := by linarith
    exact add_nonneg (mul_nonneg hr0 this) (mul_nonneg hm0 hb.le)
  have hf0 : (0 : ℝ) ≤ f := by linarith
  have hmain : max CA 0 * (3 * (f : ℝ) * r * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1))
      ≤ C * f * ((r : ℝ) * (x + S + t + η + L) + m * b) := by
    have e : 3 * (f : ℝ) * r * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1)
        = f * (3 * (r : ℝ) * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (m : ℝ) * (2 * b + 1)) := by ring
    rw [e]
    calc max CA 0 * (f * (3 * (r : ℝ) * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (m : ℝ) * (2 * b + 1)))
        ≤ max CA 0 * (f * (13 * ((r : ℝ) * (x + S + t + η + L) + m * b))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hf0) hK
      _ = (13 * max CA 0) * (f * ((r : ℝ) * (x + S + t + η + L) + m * b)) := by ring
      _ ≤ C * (f * ((r : ℝ) * (x + S + t + η + L) + m * b)) :=
          mul_le_mul_of_nonneg_right hC (mul_nonneg hf0 hB)
      _ = C * f * ((r : ℝ) * (x + S + t + η + L) + m * b) := by ring

  set Q : ℝ := (f : ℝ) ^ 2 * (t : ℝ) ^ 2 * ((r : ℝ) + t) with hQ
  have hQe : Q = (f : ℝ) ^ 2 * ((t : ℝ) ^ 2 * ((r : ℝ) + t)) := by rw [hQ]; ring
  have ht2 : (1 : ℝ) ≤ (t : ℝ) ^ 2 := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (t : ℝ) * t := mul_le_mul htR htR zero_le_one (by linarith)
      _ = (t : ℝ) ^ 2 := by ring
  have hf2 : (f : ℝ) ≤ (f : ℝ) ^ 2 := by
    calc (f : ℝ) = f * 1 := by ring
      _ ≤ (f : ℝ) * f := mul_le_mul_of_nonneg_left hfR hf0
      _ = (f : ℝ) ^ 2 := by ring
  have hrt : (1 : ℝ) ≤ (r : ℝ) + t := by linarith
  have hT1 : (1 : ℝ) ≤ (t : ℝ) ^ 2 * ((r : ℝ) + t) := one_le_mul_of_one_le_of_one_le ht2 hrt
  have hfQ : (f : ℝ) ≤ Q := by
    rw [hQe]
    exact hf2.trans (le_mul_of_one_le_right (sq_nonneg _) hT1)
  have hVQ : 4 * ((r : ℝ) + t) * t ≤ 4 * Q := by
    have h1 : ((r : ℝ) + t) * t ≤ (t : ℝ) ^ 2 * ((r : ℝ) + t) := by
      have : ((r : ℝ) + t) * t = ((r : ℝ) + t) * t * 1 := by ring
      calc ((r : ℝ) + t) * t ≤ ((r : ℝ) + t) * (t * t) :=
            mul_le_mul_of_nonneg_left (by
              calc (t : ℝ) = t * 1 := by ring
                _ ≤ (t : ℝ) * t := mul_le_mul_of_nonneg_left htR (by linarith)) (by linarith)
        _ = (t : ℝ) ^ 2 * ((r : ℝ) + t) := by ring
    have hf1 : (1 : ℝ) ≤ (f : ℝ) ^ 2 := hfR.trans hf2
    have h2 : (t : ℝ) ^ 2 * ((r : ℝ) + t) ≤ Q := by
      rw [hQe]; exact le_mul_of_one_le_left (by linarith) hf1
    linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hQL : Q ≤ Q * L := le_mul_of_one_le_right hQ0 hL.le
  have hTbQ : Tb ≤ 240 * Q * L := by
    have : 240 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * L = 240 * Q * L := by rw [hQ]; ring
    linarith
  have hpL : 260 * Q * L ≤ (p : ℝ) * L := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have : 260 * Q = (260 : ℝ) * (f : ℝ) ^ 2 * (t : ℝ) ^ 2 * ((r : ℝ) + t) := by rw [hQ]; ring
    linarith
  have hQL0 : 0 ≤ Q * L := mul_nonneg hQ0 (by linarith)
  linarith

end GlobalTheory
end

