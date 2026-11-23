module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0427
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0444
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EnvRingExists
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.EnvExist

variable {l : ℕ}

theorem iter_map {A B : Type} [CommRing A] [CommRing B] {D : Delta l A} {D' : Delta l B} {g : A →+* B}
    (hg : IsδMap D D' g) (n : ℕ) (x : A) : g (D.δ^[n] x) = D'.δ^[n] (g x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hg, ih]

theorem polyEval_isδ [Fact l.Prime] {A C : Type} [CommRing A] [CommRing C] (D : Delta l A) (DC : Delta l C)
    (f : A →+* C) (hf : IsδMap D DC f) (v : C) :
    IsδMap (polyDelta D) DC (MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v) := by
  intro x
  have : x ∈ δLocus (polyDelta D) DC (MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v) := by
    refine MvPolynomial.induction_on x ?_ ?_ ?_
    · intro a
      rw [mem_δLocus, polyDelta_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      exact hf a
    · intro p q hp hq
      exact add_mem hp hq
    · intro p k hp
      refine mul_mem hp ?_
      rw [mem_δLocus, polyDelta_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        Function.iterate_succ_apply']
  exact mem_δLocus.1 this

end GlobalTheory.BSP.EnvExist


open GlobalTheory.BSP.EnvExist in
theorem GlobalTheory.BSP.envRing_exists : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A)
    (d p : A), J.FG → (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → IsAdicComplete J A →
    Nonempty (EnvRing D J d p) := by
  intro l _ A _ D J d p hfg hl hd hδ hc
  have hstab : ∀ x ∈ Set.range (envRel D d p), (polyDelta D).δ x ∈ Ideal.span (Set.range (envRel D d p)) := by
    rintro _ ⟨k, rfl⟩
    refine Ideal.subset_span ⟨k + 1, ?_⟩
    unfold envRel
    exact Function.iterate_succ_apply' _ _ _
  obtain ⟨DL, hDL⟩ := _root_.GlobalTheory.BSP.delta_quot_span l (MvPolynomial ℕ A) (polyDelta D) _ hstab
  set mk := Ideal.Quotient.mk (Ideal.span (Set.range (envRel D d p))) with hmk
  set s : A →+* MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p)) := mk.comp MvPolynomial.C with hs
  obtain ⟨Q, _, iQ, hQ⟩ := _root_.GlobalTheory.BSP.isCompl_exists _ (J.map s) (hfg.map s)
  have hlL : ((l : ℕ) : MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p))) ∈ J.map s := by
    rw [← map_natCast s]; exact Ideal.mem_map_of_mem s hl
  obtain ⟨DQ, hDQ⟩ := _root_.GlobalTheory.BSP.exists_delta_completion l _ Q iQ (J.map s) hQ hlL DL
  have hX : ∀ k, iQ (mk (MvPolynomial.X k)) = DQ.δ^[k] (iQ (mk (MvPolynomial.X 0))) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← polyDelta_X D k, hDL, hDQ, ih, Function.iterate_succ_apply']

  have hshape := _root_.GlobalTheory.EnvShape.envRel_triangular l A D J d p hl hd hδ
  have hlev := _root_.GlobalTheory.digitMonomials_basis_mod_pow l A J (envRel D d p) hshape
  have hmono : ∀ (α : ℕ →₀ ℕ) (a : A), mk (MvPolynomial.monomial α a) = s a * mk (MvPolynomial.monomial α 1) := by
    intro α a
    rw [hs, RingHom.comp_apply, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]
  have hsum : ∀ c : Digits l →₀ A, mk (c.sum fun α a => MvPolynomial.monomial α.1 a) =
      c.sum fun α a => s a * mk (MvPolynomial.monomial α.1 1) := fun c => by
    rw [map_finsuppSum]; exact Finsupp.sum_congr fun α _ => hmono α.1 (c α)
  have hmapmem : ∀ (n : ℕ) (y : MvPolynomial ℕ A), y ∈ Ideal.span (Set.range (envRel D d p)) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) →
      mk y ∈ (J ^ n).map s := by
    intro n y hy
    have h := Ideal.mem_map_of_mem mk hy
    rwa [Ideal.map_sup, hmk, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_map] at h
  have hcomap : ∀ (n : ℕ) (y : MvPolynomial ℕ A), mk y ∈ (J ^ n).map s →
      y ∈ Ideal.span (Set.range (envRel D d p)) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
    intro n y hy
    rw [hs, ← Ideal.map_map] at hy
    have h := Ideal.mem_comap.2 hy
    rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm] at h
  obtain ⟨tb, htb⟩ := GlobalTheory.T.exists_adicTopologicalBasis_of_level_bases A (MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p))) Q s iQ J (Digits l)
    (fun α => mk (MvPolynomial.monomial α.1 1)) ⟨0, fun _ => by simpa using (Fact.out : l.Prime).pos⟩
    (by simp) hc hQ
    (fun n x => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨c, hc'⟩ := (hlev n).1 y
      refine ⟨c, ?_⟩
      have h := hmapmem n _ hc'
      rwa [map_sub, hsum] at h)
    (fun n c hcs => (hlev n).2 c (hcomap n _ (by rw [hsum]; exact hcs)))
  have hiδ : IsδMap D DQ (iQ.comp s) := by
    intro a
    show iQ (mk (MvPolynomial.C (D.δ a))) = DQ.δ (iQ (mk (MvPolynomial.C a)))
    rw [← polyDelta_C, hDL, hDQ]
  set_option synthInstance.maxHeartbeats 200000 in
  have hrel : DQ.δ ((iQ.comp s) p + (iQ.comp s) d * iQ (mk (MvPolynomial.X 0))) = 0 := by
    show DQ.δ (iQ (mk (MvPolynomial.C p)) + iQ (mk (MvPolynomial.C d)) * iQ (mk (MvPolynomial.X 0))) = 0
    have h0 : mk (envRel D d p 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨0, rfl⟩)
    rw [← map_mul iQ, ← map_mul mk, ← map_add iQ, ← map_add mk, ← hDQ, ← hDL]
    change iQ (mk (envRel D d p 0)) = 0
    rw [h0, map_zero]
  have htbb : ∀ α, tb.b α = α.1.prod fun k n => (DQ.δ^[k] (iQ (mk (MvPolynomial.X 0)))) ^ n := by
    intro α
    rw [htb α]
    show (iQ.comp mk) (MvPolynomial.monomial α.1 1) = _
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, map_finsuppProd]
    refine Finsupp.prod_congr fun k _ => ?_
    rw [map_pow, RingHom.comp_apply, hX]
  have hlift : ∀ (C : Type) [CommRing C] (DC : Delta l C) (JC : Ideal C), IsAdicComplete JC C → ∀ f : A →+* C,
      IsδMap D DC f → J.map f ≤ JC → ∀ v : C, DC.δ (f p + f d * v) = 0 →
      ∃ h : Q →+* C, IsδMap DQ DC h ∧ h.comp (iQ.comp s) = f ∧ h (iQ (mk (MvPolynomial.X 0))) = v := by
    intro C _ DC JC hC f hf hJ v hv
    have hg₀ := polyEval_isδ D DC f hf v
    set g₀ := MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v with hg₀def
    have hle : Ideal.span (Set.range (envRel D d p)) ≤ RingHom.ker g₀ := by
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      have hz : g₀ (MvPolynomial.C p + MvPolynomial.C d * MvPolynomial.X 0) = f p + f d * v := by
        simp [g₀]
      show g₀ (envRel D d p k) = 0
      rw [envRel, iter_map hg₀, Function.iterate_succ_apply, hz, hv]
      exact Function.iterate_fixed DC.δ_zero k
    set g₁ := Ideal.Quotient.lift (Ideal.span (Set.range (envRel D d p))) g₀ (fun a ha => hle ha) with hg₁def
    have hg₁C : g₁.comp s = f := RingHom.ext fun a => by
      show g₀ (MvPolynomial.C a) = f a
      exact MvPolynomial.eval₂Hom_C _ _ _
    obtain ⟨h, hh⟩ := _root_.GlobalTheory.BSP.exists_ringHom_comp_of_isCompl _ Q C iQ (J.map s) JC hQ hC g₁ (by rw [Ideal.map_map, hg₁C]; exact hJ)
    have e : ∀ z, h (iQ z) = g₁ z := fun z => RingHom.congr_fun hh z
    have hlQ : ((l : ℕ) : Q) ∈ (J.map s).map iQ := by
      rw [← map_natCast iQ]; exact Ideal.mem_map_of_mem iQ hlL
    have hJQ : ((J.map s).map iQ).map h ≤ JC := by
      rw [Ideal.map_map, hh, Ideal.map_map, hg₁C]; exact hJ
    have hhδ : IsδMap DQ DC h := GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus l Q C DQ DC ((J.map s).map iQ) JC h hlQ hJQ inferInstance
      (fun x n => by
        obtain ⟨b, hb⟩ := hQ.surj x n
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
        refine ⟨iQ (mk y), ?_, ?_⟩
        · rw [mem_δLocus, ← hDQ, ← hDL, e, e]
          exact hg₀ y
        · rw [← Ideal.map_pow]; exact hb)
    refine ⟨h, hhδ, ?_, ?_⟩
    · rw [← RingHom.comp_assoc, hh, hg₁C]
    · show h (iQ (mk (MvPolynomial.X 0))) = v
      rw [e]
      show g₀ (MvPolynomial.X 0) = v
      rw [hg₀def, MvPolynomial.eval₂Hom_X']
      rfl
  exact ⟨{ Q := Q, DQ := DQ, i := iQ.comp s, i_δ := hiδ, w := iQ (mk (MvPolynomial.X 0)), rel := hrel, tb := tb, tb_b := htbb, lift := hlift }⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfIsOfFinOrderOfCharpoly
section
noncomputable section

namespace GlobalTheory.Triple

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction.Gen
open Formalism.L2.Host (HChar CharFrame)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE)
open GlobalTheory.TripleGal (UnrRho HkFrob)

theorem eq_one_of_isOfFinOrder_of_charpoly {K : Type} [Field K] [CharZero K] {n : ℕ} {A : GL (Fin n) K}
    (hA : IsOfFinOrder A) (hc : (A : Matrix (Fin n) (Fin n) K).charpoly = (X - 1) ^ n) : A = 1 := by
  obtain ⟨m, hm, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hA
  have h1 : minpoly K (A : Matrix (Fin n) (Fin n) K) ∣ X ^ m - C 1 := minpoly.dvd _ _ (by
    rw [map_sub, map_pow, aeval_X, map_one, map_one, ← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self])
  have h2 := ((separable_X_pow_sub_C (1 : K) (Nat.cast_ne_zero.2 hm.ne') one_ne_zero).squarefree.squarefree_of_dvd
    h1).isRadical n _ (hc ▸ Matrix.minpoly_dvd_charpoly _)
  have h3 := aeval_eq_zero_of_dvd_aeval_eq_zero h2 (minpoly.aeval K _)
  rw [map_sub, aeval_X, map_one, sub_eq_zero] at h3
  exact Units.ext h3

theorem charpolyRev_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

theorem eval_charpolyRev {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (z : R) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, mul_comm z]

theorem charpolyRev_of_inv {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : A * B = 1) {m : Multiset ℂ}
    (hB : B.charpoly = (m.map fun a => X - C a).prod) : A.charpolyRev = (m.map fun a => 1 - C a⁻¹ * X).prod := by
  have e : ∀ z : ℂ, (Matrix.scalar (Fin n) z - B).det = (m.map fun a => z - a).prod := fun z => by
    rw [← Matrix.eval_charpoly, hB, eval_multiset_prod, Multiset.map_map]
    simp
  have h0 : (Matrix.scalar (Fin n) 0 - B).det ≠ 0 := by
    rw [map_zero, zero_sub, Matrix.det_neg]
    exact mul_ne_zero (by simp) (Matrix.isUnit_det_of_left_inverse h).ne_zero
  apply Polynomial.funext
  intro z
  refine mul_right_cancel₀ h0 ?_
  have e1 : (1 - z • A) * (Matrix.scalar (Fin n) 0 - B) = Matrix.scalar (Fin n) z - B := by
    rw [map_zero, zero_sub, mul_neg, sub_mul, one_mul, smul_mul_assoc, h, neg_sub, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  rw [eval_charpolyRev, ← Matrix.det_mul, e1, e, e, eval_multiset_prod, Multiset.map_map, ← Multiset.prod_map_mul]
  refine congrArg _ (Multiset.map_congr rfl fun a ha => ?_)
  have ha0 : a ≠ 0 := fun h1 => h0 (by
    rw [e]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, by rw [h1, sub_self]⟩))
  simp only [Function.comp_apply, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  field_simp
  ring

theorem sum_coeff_charpolyRev {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    ∑ k ∈ Finset.range (n + 1), M.charpolyRev.coeff k = (1 - M).det := by
  have h : M.charpolyRev.natDegree < n + 1 := by
    rw [← Matrix.reverse_charpoly, Nat.lt_succ_iff]
    exact (reverse_natDegree_le _).trans (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
  have := eval_eq_sum_range' h 1
  simp only [one_pow, mul_one, eval_charpolyRev, one_smul] at this
  exact this.symm

variable {D : D7} {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw}

theorem cyclotomicEps_eq_one_on_inertia {v : PlE D.host} (hv : v ∉ placesOver D.host.E (X.l i)) {A : ValuationSubring D.nd.Om}
    (hA : IsPlaceOver (F := D.host.E) A v) {σ : GalE D} (hσ : σ ∈ Ine (F := D.host.E) A) : eps0 X i σ = 1 := by
  have h1 : cycZ D.host.E D.nd.Om (X.l i) σ = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hv hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp
  rw [eps0, MonoidHom.comp_apply, h1, map_one]

theorem cyclotomicEps_frobenius_eq_norm {v : PlE D.host} (hv : v ∉ placesOver D.host.E (X.l i)) {A : ValuationSubring D.nd.Om}
    (hA : IsPlaceOver (F := D.host.E) A v) {σ : GalE D} (hσ : IsFrob (F := D.host.E) A (normV v) σ) :
    ((eps0 X i σ : (X.O0 i)ˣ) : X.O0 i) = (normV v : ℕ) := by
  show algebraMap ℤ_[X.l i] (X.O0 i) ((cycZ D.host.E D.nd.Om (X.l i) σ : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) = _
  rw [cycZ_of_isFrob hv hA hσ, map_natCast]

def twistW (s : X.Sig i) : GalE D →* (X.O0 i)ˣ := eps0 X i ^ D.R.t * (chiS i s)⁻¹

def matW (s : X.Sig i) (g : GalE D) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) :=
  ((twistW s g : (X.O0 i)ˣ) : X.O0 i) • ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i))

theorem matW_eq (s : X.Sig i) (g : GalE D) :
    matW s g = (((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g := by
  rw [matW, Tmat, smul_smul, twistW, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
    Units.val_pow_eq_pow_val]

theorem matW_mul_inv (s : X.Sig i) (g : GalE D) : matW s g * matW s g⁻¹ = 1 := by
  rw [matW, matW, smul_mul_smul_comm, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one,
    map_one, Units.val_one, Units.val_one, one_smul]

variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {s : X.Sig i}

section With

variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))} {ν : GalE D →* (X.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : Zbar (X.l i) →+* FbAt D w}

end With

theorem notMem_of_mem_pD {v : PlE D.host} (hv : v ∈ X.pD i) :
    v ∉ placesOver D.host.E (X.l i) ∧ ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
  have h : v ∈ placesOver D.host.E (if X.l i = D.host.pde then D.host.pde' else D.host.pde) :=
    X.pD_eq i ▸ Finset.mem_coe.2 hv
  have hl : (X.l i).Prime := (X.lPrime i).out
  split_ifs at h with e
  · exact ⟨GlobalTheory.GalChar.notMem_of_ne D.host.pde'_prime hl (e ▸ D.host.pde_ne.symm) h,
      fun k => GlobalTheory.GalChar.notMem_of_ne D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h⟩
  · exact ⟨GlobalTheory.GalChar.notMem_of_ne D.host.pde_prime hl (Ne.symm e) h,
      fun k => GlobalTheory.GalChar.notMem_of_ne D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h⟩

theorem matW_of_mem_Ine (hu : UnrRho i s) {v : PlE D.host} (hl : v ∉ placesOver D.host.E (X.l i))
    (hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k)) {A : ValuationSubring D.nd.Om}
    (hA : IsPlaceOver (F := D.host.E) A v) {g : GalE D} (hI : g ∈ Ine (F := D.host.E) A) :
    matW s g = (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
  rw [matW_eq, Tmat, cyclotomicEps_eq_one_on_inertia hl hA hI, hu v hl hg A hA g hI, Units.val_one, Units.val_one, one_pow, one_smul]

variable {Y : NExp D.R D.host D.what₂ D.LL0 D.nd X}

end GlobalTheory.Triple

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallLetterTypeFunctional
section
noncomputable section

open Polynomial Module

namespace GlobalTheory.LetterSep

theorem eq_zero_of_forall_letterHom {L U D F k : Type} [Field L] [Field U] [AddCommGroup D] [Module L D]
    (m : U →+* Module.End L D) [Field F] [Field k] [Algebra k L] [Algebra k U] [Algebra k F]
    [Algebra U F] [IsScalarTower k U F] [IsAlgClosed F] [FiniteDimensional k L]
    [Algebra.IsSeparable k L] [Module U D] [FiniteDimensional U D]
    (hm : ∀ (c : U) (x : D), c • x = m c x)
    (hk : ∀ (c : k) (x : D), m (algebraMap k U c) x = algebraMap k L c • x) (x : D)
    (hx : ∀ s : L →ₐ[k] F, ∀ f ∈ GlobalTheory.Pst.LetterDim.letterHom m (s : L →+* F) (algebraMap U F),
      f x = 0) :
    x = 0 := by
  classical
  let sm : L → D →ₗ[U] D := fun a =>
    { toFun := fun x => a • x, map_add' := smul_add a
      map_smul' := fun c x => by rw [hm, RingHom.id_apply, hm, map_smul] }
  let r : L →+* Module.End F (D →ₗ[U] F) :=
    { toFun := fun a =>
        { toFun := fun f => f ∘ₗ sm a, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      map_one' := by ext f x; simp [sm]
      map_mul' := fun a b => by ext f x; simp [sm, smul_smul, mul_comm]
      map_zero' := by ext f x; simp [sm]
      map_add' := fun a b => by ext f x; simp [sm, add_smul] }
  have hr : ∀ a f y, r a f y = f (a • y) := fun _ _ _ => rfl
  have hrk : ∀ c : k, r (algebraMap k L c) =
      algebraMap F (Module.End F (D →ₗ[U] F)) (algebraMap k F c) := fun c => by
    ext f y
    rw [hr, ← hk, ← hm, map_smul, Module.algebraMap_end_apply, LinearMap.smul_apply, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply, smul_eq_mul]
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k L
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  have hpoly : ∀ a : L, ∃ q : k[X], a = aeval α q := fun a => by
    have : a ∈ (IntermediateField.adjoin k {α}).toSubalgebra := by rw [hα]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at this
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq.symm⟩
  have hev : ∀ q : k[X], r (aeval α q) = aeval (r α) (q.map (algebraMap k F)) := fun q => by
    rw [aeval_def, aeval_def, hom_eval₂, eval₂_map]
    congr 1
    exact RingHom.ext hrk
  have hE : ∀ s : L →ₐ[k] F, (⨅ a, (r a).eigenspace (s a)) = (r α).eigenspace (s α) := fun s => by
    refine le_antisymm (iInf_le _ α) (le_iInf fun a y hy => ?_)
    obtain ⟨q, rfl⟩ := hpoly a
    rw [End.mem_eigenspace_iff] at hy ⊢
    rw [hev, End.aeval_apply_of_mem_apply_eq_smul hy, eval_map_algebraMap, aeval_algHom_apply]
  have h0 : aeval (r α) ((minpoly k α).map (algebraMap k F)) = 0 := by
    rw [← hev, minpoly.aeval, map_zero]
  have hss : (r α).IsSemisimple := End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable k α)).squarefree h0
  have htop : ⊤ ≤ ⨆ s : L →ₐ[k] F, ⨅ a, (r a).eigenspace (s a) := by
    rw [← hss.iSup_eigenspace_eq_top]
    refine iSup_le fun μ y hy => ?_
    rcases eq_or_ne y 0 with rfl | hy0
    · exact zero_mem _
    have h1 := End.aeval_apply_of_mem_apply_eq_smul (p := (minpoly k α).map (algebraMap k F))
      (End.mem_eigenspace_iff.mp hy)
    rw [h0, LinearMap.zero_apply, eq_comm, smul_eq_zero_iff_left hy0, eval_map_algebraMap] at h1
    have h2 : μ ∈ Set.range fun s : L →ₐ[k] F => s α := by
      rw [Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly F α, mem_rootSet]
      exact ⟨minpoly.ne_zero hint, h1⟩
    obtain ⟨s, rfl⟩ := h2
    exact Submodule.mem_iSup_of_mem s (by rw [hE s]; exact hy)
  by_contra hx0
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual U D, φ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 ((Module.forall_dual_apply_eq_zero_iff U x).mp h)
  let f : D →ₗ[U] F := (Algebra.linearMap U F) ∘ₗ φ
  have hf : f x ≠ 0 := by
    simp only [f, LinearMap.comp_apply, Algebra.linearMap_apply]
    exact (_root_.map_ne_zero _).mpr hφ
  apply hf
  refine Submodule.iSup_induction (motive := fun g : D →ₗ[U] F => g x = 0) _ (htop (Submodule.mem_top (x := f)))
    (fun s g hg => ?_) rfl (fun g h hg hh => by simp [hg, hh])
  have h1 : ∀ a y, g (a • y) = s a * g y := by
    intro a y
    have := (Submodule.mem_iInf _).mp hg a
    rw [End.mem_eigenspace_iff] at this
    have := LinearMap.congr_fun this y
    simpa [hr] using this
  have h2 : ∀ c y, g (m c y) = algebraMap U F c * g y := by
    intro c y
    rw [← hm, g.map_smul, Algebra.smul_def]
  exact hx s g.toAddMonoidHom ⟨h1, h2⟩

end GlobalTheory.LetterSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfLiftPeriodPowSmulIntertwiner
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.PoleBound

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {τ : Ainf l}

theorem frobW_per (hτ : bk.IsPer τ) : frobW l (inclW l τ) = bk.evW bk.E * inclW l τ := by
  rw [frobW_inclW, hτ.1, map_mul]; rfl

theorem exists_basis {d : ℕ} {S : Strat bk d} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    {T : Matrix (Fin d) (Fin d) (WCb l)} (hτ : bk.IsPer τ) (h : MReal S ρ T) :
    ∃ t : Matrix (Fin d) (Fin d) (Ainf l), t.map (inclW l) = inclW l τ ^ S.a • T := by
  have key : ∀ r j, inclW l τ ^ S.a * T r j ∈ (inclW l).range := fun r =>
    GlobalTheory.FrobIntTensor.mem_range_inclW l (fun j => inclW l τ ^ S.a * T r j)
      (Matrix.of fun j i => bk.ev (S.A i j)) fun j => by
        have e := congrFun (congrFun h.φ r) j
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e
        rw [map_mul, map_pow, frobW_per hτ, mul_pow, mul_comm (bk.evW bk.E ^ S.a), mul_assoc, e, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        change _ = bk.evW (S.A i j) * _
        ring
  choose t ht using key
  exact ⟨Matrix.of t, Matrix.ext fun r j => ht r j⟩

theorem exists_inv {d : ℕ} {S : Strat bk d} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    {T U : Matrix (Fin d) (Fin d) (WCb l)} (hτ : bk.IsPer τ) (h : MReal S ρ T) (hU : U * T = 1) (hT : T * U = 1) :
    ∃ t : Matrix (Fin d) (Fin d) (Ainf l), t.map (inclW l) = inclW l τ ^ S.b • U := by
  have h1 : U.map (frobW l) * T.map (frobW l) = 1 := by
    rw [← Matrix.map_mul (f := frobW l), hU, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : S.A.map bk.evW * S.A'.map bk.evW = bk.evW bk.E ^ S.b • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← Matrix.map_mul (f := bk.evW), S.A_mul]
    ext1 i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, Matrix.one_apply]
    split_ifs <;> simp
  have h3 : bk.evW bk.E ^ S.b • U.map (frobW l) = bk.evW bk.E ^ S.a • (S.A'.map bk.evW * U) := by
    have e := congrArg (fun M => U.map (frobW l) * (M * S.A'.map bk.evW) * U) h.φ
    simp only [Matrix.mul_assoc T, h2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at e
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, hT, Matrix.mul_one] at e
    exact e.symm
  have key : ∀ r j, inclW l τ ^ S.b * U j r ∈ (inclW l).range := fun r =>
    GlobalTheory.FrobIntTensor.mem_range_inclW l (fun j => inclW l τ ^ S.b * U j r)
      (Matrix.of fun j i => bk.ev (bk.E ^ S.a * S.A' j i)) fun j => by
        have e := congrFun (congrFun h3 j) r
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e
        rw [map_mul, map_pow, frobW_per hτ, mul_pow, mul_comm (bk.evW bk.E ^ S.b), mul_assoc, e, Finset.mul_sum,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        change _ = bk.evW (bk.E ^ S.a * S.A' j i) * _
        rw [map_mul, map_pow]
        ring
  choose t ht using key
  exact ⟨Matrix.of fun j r => t r j, Matrix.ext fun j r => ht r j⟩

theorem exists_pow_smul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l))
    (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' →
    ∀ (f : Matrix (Fin d') (Fin d) ℤ_[l]) (X : Matrix (Fin d') (Fin d) (WCb l)), T' * X = zW f * T →
    ∃ (M : ℕ) (x : Matrix (Fin d') (Fin d) (Ainf l)), x.map (inclW l) = inclW l τ ^ M • X := by
  intro l _ K bk τ hτ d d' S S' ρ ρ' T T' h h' f X hX
  obtain ⟨V, hV⟩ := h'.unit
  have hU : (V⁻¹ : _ˣ).1 * T' = 1 := hV ▸ V.inv_mul
  have hT : T' * (V⁻¹ : _ˣ).1 = 1 := hV ▸ V.mul_inv
  obtain ⟨t, ht⟩ := exists_basis hτ h
  obtain ⟨u, hu⟩ := exists_inv hτ h' hU hT
  have hf : (f.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW f :=
    Matrix.ext fun i j => (inclWA l).commutes (f i j)
  refine ⟨S'.b + S.a, u * (f.map (algebraMap ℤ_[l] (Ainf l)) * t), ?_⟩
  rw [Matrix.map_mul, Matrix.map_mul, ht, hu, hf, Matrix.mul_smul, ← hX, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_assoc, hU, Matrix.one_mul, smul_smul, pow_add]

end GlobalTheory.BSP.PoleBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveRootsOfNcardRootSetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_roots_of_ncard_rootSet' : ∀ {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Algebra A O] (t : ℕ) (P : Polynomial A) (α : Fin t → FractionRing O), Function.Injective (algebraMap A O) → ((P.map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t → P.map ((toFr O).comp (algebraMap A O)) = ∏ c, (Polynomial.X - Polynomial.C (α c)) → ∃ β : Fin t → O, Function.Injective β ∧ P.map (algebraMap A O) = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  first | exact @GlobalTheory.exists_injective_roots_of_ncard_rootSet | exact GlobalTheory.exists_injective_roots_of_ncard_rootSet | (intros; apply GlobalTheory.exists_injective_roots_of_ncard_rootSet <;> assumption)
end

