module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0540

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaximalIdealIff
section
noncomputable section

namespace GlobalTheory.TripleAdm

open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.CyclotomicNorms (Fbar rootsBar IsGood IrredOn BB primeToPart)
open GlobalTheory.TameLabels GlobalTheory.TripleResidual

section Algebra

variable {g : ℕ} [Fact g.Prime]

theorem nodup_rootsBar {f : (ZMod g)[X]} (hf : Squarefree f) : (rootsBar f).Nodup :=
  nodup_roots ((separable_map _).2 (PerfectField.separable_iff_squarefree.2 hf))

theorem exists_dvd_of_stable {K : Type} [Field K] {N : ℕ} {f : (ZMod g)[X]} (hf : Squarefree f) (a : Fbar g →* K)
    (ha : ∀ x ∈ rootsBar f, ∀ y ∈ rootsBar f, a x = a y → x = y) (T P : GL (Fin N) K) (hP : P * T * P⁻¹ = T ^ g)
    (hT : (T : Matrix (Fin N) (Fin N) K).charpoly = ((rootsBar f).map fun x => X - C (a x)).prod)
    (W : Submodule K (Fin N → K)) (hTW : ∀ x ∈ W, (T : Matrix (Fin N) (Fin N) K).mulVec x ∈ W)
    (hPW : ∀ x ∈ W, ((P⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).mulVec x ∈ W) :
    ∃ q : (ZMod g)[X], q ∣ f ∧ q.natDegree = Module.finrank K W := by
  classical
  let t : Module.End K (Fin N → K) := Matrix.toLin' (T : Matrix (Fin N) (Fin N) K)
  have ht : ∀ x ∈ W, t x ∈ W := hTW
  set p := LinearMap.charpoly (t.restrict ht) with hp
  have hT' : (T : Matrix (Fin N) (Fin N) K).charpoly = (((rootsBar f).map a).map fun x => X - C x).prod := by
    rw [hT, Multiset.map_map]; rfl
  have hdvd : p ∣ (((rootsBar f).map a).map fun x => X - C x).prod := by
    rw [← hT', ← Matrix.charpoly_toLin', GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ W t ht]
    exact dvd_mul_right _ _
  have h0 : (((rootsBar f).map a).map fun x => X - C x).prod ≠ 0 := hT' ▸ (Matrix.charpoly_monic _).ne_zero
  have hle : p.roots ≤ (rootsBar f).map a := by
    have := roots.le_of_dvd h0 hdvd
    rwa [roots_multiset_prod_X_sub_C] at this
  have hcard : p.roots.card = Module.finrank K W := by
    rw [← LinearMap.charpoly_natDegree (t.restrict ht)]
    refine (Splits.natDegree_eq_card_roots ?_).symm
    exact Splits.of_dvd (Splits.multisetProd fun x hx => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
      exact Splits.X_sub_C _) h0 hdvd
  have hnd := nodup_rootsBar hf
  let S := (rootsBar f).filter fun x => a x ∈ p.roots
  have hS : S.map a = p.roots := by
    have h1 : ((rootsBar f).map a).Nodup := hnd.map_on ha
    rw [Multiset.Nodup.ext (Multiset.nodup_of_le (Multiset.map_le_map (Multiset.filter_le _ _)) h1)
      (Multiset.nodup_of_le hle h1)]
    intro z
    rw [Multiset.mem_map]
    refine ⟨?_, fun hz => ?_⟩
    · rintro ⟨x, hx, rfl⟩
      exact (Multiset.mem_filter.1 hx).2
    · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_of_le hle hz)
      exact ⟨x, Multiset.mem_filter.2 ⟨hx, hz⟩, rfl⟩
  have hroot : ∀ c, c ∈ p.roots ↔ ∃ w ∈ W, w ≠ 0 ∧ (T : Matrix (Fin N) (Fin N) K).mulVec w = c • w := fun c => by
    rw [mem_roots (LinearMap.charpoly_monic _).ne_zero, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨w, hw⟩ := h.exists_hasEigenvector
      exact ⟨w.1, w.2, fun h => hw.2 (Subtype.ext h), congrArg Subtype.val hw.apply_eq_smul⟩
    · rintro ⟨w, hw, h1, h2⟩
      exact Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨w, hw⟩)
        ⟨Module.End.mem_eigenspace_iff.2 (Subtype.ext h2), fun h => h1 (congrArg Subtype.val h)⟩
  have hst : ∀ x ∈ S, x ^ g ∈ S := fun x hx => by
    obtain ⟨hx1, hx2⟩ := Multiset.mem_filter.1 hx
    refine Multiset.mem_filter.2 ⟨GlobalTheory.TameLabels.rootsBar_frob f ▸ Multiset.mem_map_of_mem _ hx1, ?_⟩
    obtain ⟨w, hw, h1, h2⟩ := (hroot _).1 hx2
    have h3 : ∀ n : ℕ, ((T ^ n : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).mulVec w = a x ^ n • w := fun n => by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, ih, smul_smul,
          pow_succ']
    refine (hroot _).2 ⟨_, hPW w hw, fun h => h1 ?_, ?_⟩
    · rw [← Matrix.one_mulVec w, ← Units.val_one, ← mul_inv_cancel P, Units.val_mul, ← Matrix.mulVec_mulVec, h,
        Matrix.mulVec_zero]
    · rw [Matrix.mulVec_mulVec, ← Units.val_mul, show T * P⁻¹ = P⁻¹ * T ^ g by rw [← hP]; group, Units.val_mul,
        ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_smul, map_pow]
  have hSn : S.Nodup := hnd.filter _
  obtain ⟨q, hq, hqS⟩ := GlobalTheory.Compare.TeichmullerRoots.exists_monic_of_stable S (by
    refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset (hSn.map (frobenius (Fbar g) g).injective)).2 ?_)
      (Multiset.card_map _ _).ge
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy
    exact hst x hx)
  refine ⟨q, ?_, by rw [← GlobalTheory.TameLabels.card_rootsBar, hqS, ← hcard, ← hS, Multiset.card_map]⟩
  rw [← map_dvd_map' (algebraMap (ZMod g) (Fbar g))]
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots (hq.map _).ne_zero ?_
  exact hqS.trans_le (Multiset.filter_le _ _)

theorem irredOn_of_labels {l N : ℕ} [Fact l.Prime] {PP Γ : Type} [Group Γ] {f : PP → (ZMod g)[X]}
    (hd : ∀ v, (f v).natDegree = N) (hf : ∀ v, Squarefree (f v))
    (h4 : ∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ ∃ q : (ZMod g)[X], q ∣ f v ∧ q.natDegree = a)
    (a : PP → Fbar g →* Fbar l) (ha : ∀ v, ∀ x ∈ rootsBar (f v), ∀ y ∈ rootsBar (f v), a v x = a v y → x = y)
    (ρ : Γ →* GL (Fin N) (Fbar l)) (τ : PP → Γ) (hφ : ∀ v, ∃ φ, ρ (φ * τ v * φ⁻¹) = ρ (τ v) ^ g)
    (hτ : ∀ v, ((ρ (τ v) : GL (Fin N) (Fbar l)) : Matrix (Fin N) (Fin N) (Fbar l)).charpoly =
      ((rootsBar (f v)).map fun x => X - C (a v x)).prod) : IrredOn ρ ⊤ := by
  intro W hW
  have key : ∀ v, ∃ q : (ZMod g)[X], q ∣ f v ∧ q.natDegree = Module.finrank (Fbar l) W := fun v => by
    obtain ⟨φ, h⟩ := hφ v
    rw [map_mul, map_mul, map_inv] at h
    exact exists_dvd_of_stable (hf v) (a v) (ha v) _ _ h (hτ v) W (hW _ trivial)
      (by rw [← map_inv]; exact hW _ trivial)
  have hle : Module.finrank (Fbar l) W ≤ N := by simpa using W.finrank_le
  by_contra hc
  rw [not_or] at hc
  have h0 : Module.finrank (Fbar l) W ≠ 0 := fun h => hc.1 (Submodule.finrank_eq_zero.1 h)
  have h1 : Module.finrank (Fbar l) W ≠ N := fun h => hc.2 (Submodule.eq_top_of_finrank_eq (by simpa using h))
  by_cases h : 2 * Module.finrank (Fbar l) W ≤ N
  · obtain ⟨v, hv⟩ := h4 _ (by omega) h
    exact hv (key v)
  · obtain ⟨v, hv⟩ := h4 (N - Module.finrank (Fbar l) W) (by omega) (by omega)
    obtain ⟨q, ⟨q', hq⟩, hqa⟩ := key v
    have hne : q * q' ≠ 0 := hq ▸ (hf v).ne_zero
    have hdeg := hd v
    rw [hq, natDegree_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)] at hdeg
    exact hv ⟨q', Dvd.intro_left _ hq.symm, by omega⟩

theorem primeToPart_eq_of_eq {l : ℕ} [Fact l.Prime] (a : Fbar g →* Fbar l)
    (ha : ∀ x y, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime l → (orderOf y).Coprime l → a x = a y → x = y)
    {x y : Fbar g} (hx : x ≠ 0) (hy : y ≠ 0) (h : a x = a y) : primeToPart l x = primeToPart l y := by
  have key : ∀ x : Fbar g, x ≠ 0 → primeToPart l x ≠ 0 ∧ (orderOf (primeToPart l x)).Coprime l := fun x hx => by
    obtain ⟨-, M, -, h1, h2, -⟩ := GlobalTheory.TameRed.part_spec (Fact.out : l.Prime) (isOfFinOrder_of_ne_zero hx)
    exact ⟨pow_ne_zero _ hx, h1.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h2)⟩
  refine ha _ _ (key x hx).1 (key y hy).1 (key x hx).2 (key y hy).2 ?_
  rw [GlobalTheory.TypeLeaf.map_primeToPart_fbar, GlobalTheory.TypeLeaf.map_primeToPart_fbar, h]

theorem charpoly_smul_congr {K : Type} [Field K] [Infinite K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (c : Kˣ)
    (h : A.charpoly = B.charpoly) : ((c : K) • A).charpoly = ((c : K) • B).charpoly := by
  have e : ∀ (M : Matrix (Fin n) (Fin n) K) (z : K), Matrix.scalar (Fin n) z - (c : K) • M =
      (c : K) • (Matrix.scalar (Fin n) (z / c) - M) := fun M z => by
    rw [smul_sub, Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
    congr 2
    funext x
    simp [mul_div_cancel₀ _ c.ne_zero]
  refine Polynomial.funext fun z => ?_
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly, e, e, Matrix.det_smul, Matrix.det_smul, ← Matrix.eval_charpoly,
    ← Matrix.eval_charpoly, h]

end Algebra

open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf IsReduction Zbar GalE toFb)
open GlobalTheory.Triple (IsParam IsResidual Reading IsChars IsTripleWith IsTripleFor IsTripleOf IsTriple muBase hframe jIdx)
open GlobalTheory.TwistDet GlobalTheory.GalChar Formalism.L2.Host

variable {D : D7}

section Row

variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {w : D.what₂.places.Pl}

theorem root_ne_zero (hg : D.nd.goodRow σ) (k : Fin 2) (v : D.nd.PlG k) {x : Fb (D.host.g k) (D.host.g_prime k)}
    (hx : x ∈ @rootsBar _ ⟨D.host.g_prime k⟩ (D.nd.lab k σ v)) : x ≠ 0 := by
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  rintro rfl
  exact ((hg k).1.1 v).2.2 ((GlobalTheory.Compare.TeichmullerRoots.zero_mem_rootsBar ((hg k).1.1 v).1).1 hx)

theorem toFb_ne_zero (k : Fin 2) (u : (ZMod (D.host.g k))ˣ) : toFb D k u ≠ 0 :=
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  (map_ne_zero_iff _ (algebraMap (ZMod (D.host.g k)) (Fbar (D.host.g k))).injective).2 u.ne_zero

end Row

section Comparison₂

variable {Y : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : Y.Tw} {b : Bool}

theorem norm_toQ_le (ρ : Reading Y i b) (x : Y.O0 i) : ‖toQ ρ.κ x‖ ≤ 1 := by
  have h : IsIntegral ℤ_[Y.l i] x := Algebra.IsIntegral.isIntegral x
  let f : Y.O0 i →ₐ[ℤ_[Y.l i]] Qbar (Y.l i) := { toQ ρ.κ with commutes' := ρ.κ_alg }
  obtain ⟨p, hp, h0⟩ : IsIntegral ℤ_[Y.l i] (toQ ρ.κ x) := h.map f
  let v := NormedField.valuation (K := Qbar (Y.l i))
  let z : ℤ_[Y.l i] →+* v.integer := (algebraMap ℤ_[Y.l i] (Qbar (Y.l i))).codRestrict _ fun a => by
    change ‖algebraMap ℚ_[Y.l i] (Qbar (Y.l i)) (a : ℚ_[Y.l i])‖ ≤ 1
    rw [norm_algebraMap']
    exact a.2
  exact (Valuation.integer.integers v).mem_of_integral ⟨p.map z, hp.map z, by rw [eval₂_map]; exact h0⟩

def toZ (ρ : Reading Y i b) : Y.O0 i →+* Zbar (Y.l i) := (toQ ρ.κ).codRestrict _ (norm_toQ_le ρ)

theorem mem_maximalIdeal_iff (ρ : Reading Y i b) (x : Y.O0 i) :
    x ∈ IsLocalRing.maximalIdeal (Y.O0 i) ↔ ‖toQ ρ.κ x‖ < 1 := by
  obtain ⟨-, -, hint, -⟩ := GlobalTheory.CoefEmbed.embedding_closed_integral _ _ (Y.twistBaseCoefficientRing_isAdic i) ρ.κ ρ.κ_alg
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← not_le, not_iff_not]
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨u, rfl⟩
    have h1 : ‖toQ ρ.κ u‖ * ‖toQ ρ.κ (u⁻¹ : (Y.O0 i)ˣ)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    nlinarith [norm_toQ_le ρ (u⁻¹ : (Y.O0 i)ˣ), norm_nonneg (toQ ρ.κ u)]
  · have h0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero, norm_zero] at h
      exact absurd h (by norm_num)
    obtain ⟨y, hy⟩ := hint (algebraMap (Y.O0 i) (FractionRing (Y.O0 i)) x)⁻¹ (by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ h)
    refine IsUnit.of_mul_eq_one y (IsFractionRing.injective _ (FractionRing (Y.O0 i)) ?_)
    rw [map_mul, hy, map_one, mul_inv_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 h0)]

theorem exists_residue_lift (ρ : Reading Y i b) {K : Type} [Field K] (f : Y.O0 i →+* K) (hl : ((Y.l i : ℕ) : K) = 0) :
    ∃ κ : IsLocalRing.ResidueField (Y.O0 i) →+* K, ∀ x, κ (IsLocalRing.residue _ x) = f x := by
  have h0 : RingHom.ker f ≠ ⊥ := fun h => by
    have h1 : ((Y.l i : ℕ) : Y.O0 i) ∈ RingHom.ker f := by rw [RingHom.mem_ker, map_natCast, hl]
    rw [h, Ideal.mem_bot] at h1
    have h2 := congrArg (toQ ρ.κ) h1
    rw [map_natCast, map_zero] at h2
    exact (Y.lPrime i).out.ne_zero (by exact_mod_cast h2)
  have h1 := IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime f).isMaximal h0)
  exact ⟨Ideal.Quotient.lift _ f fun x hx => by rwa [← h1] at hx, fun _ => rfl⟩

variable {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}

theorem antiHom_of_isLAdicOf (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {χ : HChar D.host.E} {n : (D.host.E →+* ℂ) → ℤ} {r : GalE D →* (Qbar l)ˣ} (hc : Continuous r)
    (h : GlobalTheory.HeckeGal.IsLAdicOf art ι χ n r) (ht : χ.TrivOn D.host.F) : AntiHom Y.cc r := by
  obtain ⟨c, hc1, hcm, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have h1 : ∀ x : D.host.E, Y.cc (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (c x) := fun x => by
    obtain ⟨j, hj⟩ := Y.cc_cm.1
    apply j.injective
    rw [hj, hc1]
    exact (D.host.conjE_apply (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
  exact GlobalTheory.AntiLAdic.antiHom_of_trivOn D.host.F D.host.E c hcm.rank hcm.ne (fun x => by rw [hc1, hc1, conj_conj]) hr
    D.nd.Om Y.cc h1 art ha l ι χ n _ hc h ht

variable {Z : NExp D.R D.host D.what₂ D.LL0 D.nd Y}

end Comparison₂

end GlobalTheory.TripleAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproduct
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EnvCop

section
variable {l : ℕ}

theorem map_eq_span {A C : Type} [CommRing A] [CommRing C] (f : A →+* C) (I : Ideal A) (d : A)
    (hI : I = Ideal.span {d}) : I.map f = Ideal.span {f d} := by
  subst hI; rw [Ideal.map_span, Set.image_singleton]

theorem map_sup_le {A C : Type} [CommRing A] [CommRing C] (f : A →+* C) (I : Ideal A) (I' : Ideal C)
    (h : ∀ a ∈ I, f a ∈ I') : (Ideal.span {(l : A)} ⊔ I).map f ≤ Ideal.span {(l : C)} ⊔ I' := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast]
  exact sup_le_sup_left (Ideal.map_le_of_le_comap fun a ha => Ideal.mem_comap.2 (h a ha)) _

theorem eq_add_mul_of {R : Type} [CommRing R] {a b c v : R} (h : v * c = a - b) : a = b + c * v := by
  linear_combination -h

theorem map_span_mem {Q C : Type} [CommRing Q] [CommRing C] (h : Q →+* C) (q : Q) (I : Ideal C)
    (hq : h q ∈ I) : ∀ a ∈ Ideal.span {q}, h a ∈ I := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [map_mul]; exact Ideal.mul_mem_left _ _ hq

theorem quot_eq_of {Q C : Type} [CommRing Q] [CommRing C] (h : Q →+* C) (I : Ideal C) (a b : Q) (c : C)
    (hb : h b = c) (e : h (a - b) ∈ I) : Ideal.Quotient.mk I (h a) = Ideal.Quotient.mk I c := by
  subst hb; rw [map_sub] at e; exact Ideal.Quotient.eq.2 e

theorem eval_lin {Q C : Type} [CommRing Q] [CommRing C] (h : Q →+* C) (x P D w : Q) (p d v : C)
    (hx : x = P + D * w) (hP : h P = p) (hD : h D = d) (hw : h w = v) : h x = p + d * v := by
  subst hx hP hD hw; rw [map_add (f := _), map_mul]

theorem cancel_of {C : Type} [CommRing C] {p d a v : C} (hd : d ∈ nonZeroDivisors C)
    (h : p + d * a = p + d * v) : a = v := by
  have e : d * (a - v) = 0 := by rw [mul_sub]; exact sub_eq_zero.2 (add_left_cancel h)
  exact sub_eq_zero.1 (hd.1 _ e)

theorem fg_sup_span {A : Type} [CommRing A] (I : Ideal A) (d : A) (hI : I = Ideal.span {d}) :
    (Ideal.span {(l : A)} ⊔ I).FG := by
  subst hI; exact (Submodule.fg_span_singleton _).sup (Submodule.fg_span_singleton _)
end

theorem comp_hf_X {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {P P' : Obj l ↥(OL K)} (h' : Hom P P')
    (g0 : Hom bk.prism P) (g : Hom bk.prism P') (h2 : h'.comp g0 = g) : h'.f (BK.hf g0 X) = BK.hf g X := by
  subst h2; rfl

section

variable {l : ℕ}

theorem quot_bdd_of_mem {A : Type} [CommRing A] (q : A) (N : ℕ)
    (h : ∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {q} → (l : A) ^ N * x ∈ Ideal.span {q}) :
    ∀ x : A ⧸ Ideal.span {q}, (∃ m : ℕ, (l : A ⧸ Ideal.span {q}) ^ m * x = 0) →
      (l : A ⧸ Ideal.span {q}) ^ N * x = 0 := by
  rintro x ⟨m, hm⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hm' : (l : A) ^ m * y ∈ Ideal.span {q} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast]; exact hm
  have h2 := h y m hm'
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast] at h2
  exact h2

theorem pow_mul_mem_of_pow_mul_mem {A : Type} [CommRing A] (I : Ideal A) (N : ℕ)
    (h : ∀ x : A ⧸ I, (∃ m : ℕ, (l : A ⧸ I) ^ m * x = 0) → (l : A ⧸ I) ^ N * x = 0) :
    ∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ I → (l : A) ^ N * x ∈ I := by
  intro x m hm
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast] at hm ⊢
  exact h _ ⟨m, hm⟩

theorem map_sup_span {A Q : Type} [CommRing A] [CommRing Q] (i : A →+* Q) (I : Ideal A) (d : A)
    (hI : I = Ideal.span {d}) :
    (Ideal.span {(l : A)} ⊔ I).map i = Ideal.span {(l : Q)} ⊔ Ideal.span {i d} := by
  subst hI
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast]

theorem le_comap_span {A Q : Type} [CommRing A] [CommRing Q] (i : A →+* Q) (I : Ideal A) (d : A)
    (hI : I = Ideal.span {d}) : I ≤ (Ideal.span {i d}).comap i := by
  subst hI
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [Ideal.mem_comap, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {B : Obj l ↥(OL K)} {d p : B.A}

section
variable (hI : B.I = Ideal.span {d}) (En : EnvRing B.D (JJ B) d p)
include hI

theorem facts : ∃ N : ℕ, En.i d ∈ nonZeroDivisors En.Q ∧ ∀ (x : En.Q) (m : ℕ),
    (l : En.Q) ^ m * x ∈ Ideal.span {En.i d} → (l : En.Q) ^ N * x ∈ Ideal.span {En.i d} := by
  obtain ⟨N, hN⟩ := B.bdd
  have hnz : d ∈ nonZeroDivisors B.A := by
    have h := B.inv; rw [hI] at h; exact _root_.GlobalTheory.BSP.mem_nonZeroDivisors_of_invertible_span_singleton _ d h
  have hb : ∀ (x : B.A) (m : ℕ), (l : B.A) ^ m * x ∈ Ideal.span {d} → (l : B.A) ^ N * x ∈ Ideal.span {d} := by
    rw [← hI]; exact pow_mul_mem_of_pow_mul_mem B.I N hN
  have tb : TopBasis En.i (Ideal.span {(l : B.A)} ⊔ Ideal.span {d}) (Digits l) := by
    rw [← hI]; exact En.tb
  exact ⟨N, GlobalTheory.T.regular_and_bounded_torsion_of_adicTopologicalBasis l B.A En.Q En.i d N (Digits l) hnz hb tb⟩

def strQ : ↥(OL K) →+* En.Q ⧸ Ideal.span {En.i d} :=
  (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hI)).comp B.str

theorem strQ_eq (r : ↥(OL K)) (b : B.A) (hb : Ideal.Quotient.mk B.I b = B.str r) :
    strQ hI En r = Ideal.Quotient.mk (Ideal.span {En.i d}) (En.i b) :=
  (congrArg (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hI)) hb).symm.trans
    Ideal.quotientMap_mk

abbrev obj : Obj l ↥(OL K) where
  A := En.Q
  D := En.DQ
  I := Ideal.span {En.i d}
  inv := invertible_span_singleton (facts hI En).choose_spec.1
  complete := by rw [← map_sup_span En.i B.I d hI]; exact En.tb.complete
  l_mem := En.DQ.l_mem_of_isUnit hl.out.pos (by rw [← En.i_δ d]; exact (GlobalTheory.T.isUnit_delta_of_prism_ideal_eq_span l _ B d hI).map En.i)
  bdd := ⟨(facts hI En).choose, quot_bdd_of_mem (En.i d) _ (facts hI En).choose_spec.2⟩
  str := strQ hI En

def inl : Hom B (obj hI En) where
  f := En.i
  f_δ := En.i_δ
  f_I a ha := le_comap_span En.i B.I d hI ha
  f_str r a h := Ideal.quotientMap_mk.symm.trans
    (congrArg (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hI)) h)

end

variable {bk : BK K} (En : EnvRing B.D (JJ B) d p)

theorem frame (hF : IsFrame bk B d p) : IsFrame bk (obj hF.1 En) (En.i d) (En.i p + En.i d * En.w) := by
  refine ⟨rfl, ?_⟩
  have e1 := congrArg (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hF.1)) hF.2
  have e2 : En.i p + En.i d * En.w - En.i p ∈ Ideal.span {En.i d} := by
    rw [add_sub_cancel_left]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  exact (Ideal.Quotient.eq.2 e2).trans (Ideal.quotientMap_mk.symm.trans e1)

theorem str_of (hI : B.I = Ideal.span {d}) {C : Obj l ↥(OL K)} (f : Hom B C) (h0 : En.Q →+* C.A)
    (h0a : ∀ a, h0 (En.i a) = f.f a) (hIQ : ∀ a ∈ Ideal.span {En.i d}, h0 a ∈ C.I) (r : ↥(OL K)) (a : En.Q)
    (ha : Ideal.Quotient.mk (Ideal.span {En.i d}) a = strQ hI En r) :
    Ideal.Quotient.mk C.I (h0 a) = C.str r := by
  have hsu : ∃ b : B.A, Ideal.Quotient.mk B.I b = B.str r := Ideal.Quotient.mk_surjective (B.str r)
  obtain ⟨b, hb⟩ := hsu
  have e1 : Ideal.Quotient.mk (Ideal.span {En.i d}) a = Ideal.Quotient.mk (Ideal.span {En.i d}) (En.i b) :=
    ha.trans (strQ_eq hI En r b hb)
  have hab : a - En.i b ∈ Ideal.span {En.i d} := Ideal.Quotient.eq.1 e1
  exact (quot_eq_of h0 C.I a (En.i b) (f.f b) (h0a b) (hIQ _ hab)).trans (f.f_str r b hb)

theorem I_of (hI : B.I = Ideal.span {d}) {C : Obj l ↥(OL K)} (f : Hom B C) (h0 : En.Q →+* C.A)
    (h0a : ∀ a, h0 (En.i a) = f.f a) : ∀ a ∈ Ideal.span {En.i d}, h0 a ∈ C.I :=
  map_span_mem h0 (En.i d) C.I ((congrArg (· ∈ C.I) (h0a d)).mpr
    (f.f_I d (by rw [hI]; exact Ideal.mem_span_singleton_self d)))

def lift (hI : B.I = Ideal.span {d}) {C : Obj l ↥(OL K)} (f : Hom B C) (h0 : En.Q →+* C.A)
    (h0δ : IsδMap En.DQ C.D h0) (h0a : ∀ a, h0 (En.i a) = f.f a) : Hom (obj hI En) C where
  f := h0
  f_δ := h0δ
  f_I := I_of En hI f h0 h0a
  f_str := str_of En hI f h0 h0a (I_of En hI f h0 h0a)


set_option maxHeartbeats 2000000 in
theorem univ (hF : IsFrame bk B d p) (g0 : Hom bk.prism (obj hF.1 En))
    (hg0 : BK.hf g0 X = En.i p + En.i d * En.w) (C : Obj l ↥(OL K)) (f : Hom B C)
    (g : Hom bk.prism C) : ∃! h : Hom (obj hF.1 En) C, h.comp (inl hF.1 En) = f ∧ h.comp g0 = g := by
  have hdI : d ∈ B.I := by rw [hF.1]; exact Ideal.mem_span_singleton_self d
  have hCI : C.I = Ideal.span {f.f d} :=
    (GlobalTheory.T.prism_hom_map_ideal_eq l _ B C f).symm.trans (map_eq_span f.f B.I d hF.1)
  have hnz : f.f d ∈ nonZeroDivisors C.A := by
    have h := C.inv; rw [hCI] at h; exact _root_.GlobalTheory.BSP.mem_nonZeroDivisors_of_invertible_span_singleton _ _ h
  obtain ⟨hgδ, hgs⟩ := GlobalTheory.T.breuilKisinHom_image_X_delta_zero_lifts_uniformizer l K bk C g
  have hfp := f.f_str _ p hF.2
  have hmem : BK.hf g X - f.f p ∈ Ideal.span {f.f d} := by
    rw [← hCI]; exact Ideal.Quotient.eq.1 (hgs.trans hfp.symm)
  have hex : ∃ v', v' * f.f d = BK.hf g X - f.f p := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨v', hv'⟩ := hex
  have hgX : BK.hf g X = f.f p + f.f d * v' := eq_add_mul_of hv'
  have hrel : C.D.δ (f.f p + f.f d * v') = 0 := (congrArg C.D.δ hgX).symm.trans hgδ
  have hJ : (JJ B).map f.f ≤ JJ C := map_sup_le f.f B.I C.I f.f_I
  have hlift : ∃ h : En.Q →+* C.A, IsδMap En.DQ C.D h ∧ h.comp En.i = f.f ∧ h En.w = v' :=
    En.lift C.A C.D (JJ C) C.complete f.f f.f_δ hJ v' hrel
  obtain ⟨h0, h0δ, h0i, h0w⟩ := hlift
  have h0a : ∀ a, h0 (En.i a) = f.f a := fun a => RingHom.congr_fun h0i a
  refine ⟨lift En hF.1 f h0 h0δ h0a, ⟨Hom.ext' h0i, _root_.GlobalTheory.BSP.BK.hom_ext_of_hf_X l K bk C _ _ ?_⟩, ?_⟩
  · exact (eval_lin h0 _ _ _ _ _ _ _ hg0 (h0a p) (h0a d) h0w).trans hgX.symm
  · rintro h' ⟨h1, h2⟩
    have e1 : h'.f.comp En.i = f.f := congrArg Hom.f h1
    have e1a : ∀ a, h'.f (En.i a) = f.f a := fun a => RingHom.congr_fun e1 a
    have e2 := comp_hf_X h' g0 g h2
    have e3 : h'.f En.w = v' :=
      cancel_of hnz ((eval_lin h'.f (BK.hf g0 X) (En.i p) (En.i d) En.w (f.f p) (f.f d) (h'.f En.w) hg0 (e1a p) (e1a d) rfl).symm.trans (e2.trans hgX))
    have hJ' : (JJ B).map (h'.f.comp En.i) ≤ JJ C := (congrArg (fun φ => (JJ B).map φ ≤ JJ C) e1).mpr hJ
    exact Hom.ext' (_root_.GlobalTheory.BSP.deltaHom_unique_of_base l B.A En.Q C.A En.DQ C.D (JJ B) (JJ C) En.i En.w En.tb En.tb_b
      C.complete.toIsHausdorff h'.f h0 h'.f_δ h0δ hJ' (e1.trans h0i.symm) (e3.trans h0w.symm))

def env (hF : IsFrame bk B d p) : Env bk B d p :=
  have hex := GlobalTheory.T.exists_breuilKisinHom_of_uniformizerFrame l K bk (obj hF.1 En) (En.i d) (En.i p + En.i d * En.w) (frame En hF) En.rel
  { Q := obj hF.1 En
    inl := inl hF.1 En
    inr := hex.choose
    univ := univ En hF hex.choose hex.choose_spec
    w := En.w
    w_eq := hex.choose_spec
    I_eq := rfl
    tb := En.tb
    tb_b := En.tb_b }

end GlobalTheory.BSP.EnvCop


open GlobalTheory.BSP.EnvCop in
theorem GlobalTheory.BSP.nonempty_env : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
    (d p : B.A), IsFrame bk B d p → Nonempty (Env bk B d p) := by
  intro l _ K bk B d p hF
  have hd : d ∈ JJ B := Ideal.mem_sup_right (by rw [hF.1]; exact Ideal.mem_span_singleton_self d)
  have hEn : Nonempty (EnvRing B.D (JJ B) d p) :=
    _root_.GlobalTheory.BSP.envRing_exists l B.A B.D (JJ B) d p (fg_sup_span B.I d hF.1)
      (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (l : B.A))) hd (GlobalTheory.T.isUnit_delta_of_prism_ideal_eq_span l _ B d hF.1) B.complete
  exact ⟨env hEn.some hF⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedHomDefectFrobeniusEquationStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stratifiedHom_defect_frobenius_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (Y : Matrix (Fin d') (Fin d) bk.S), bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A) → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * (S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g).map B.D.φ) = BK.hf f bk.E ^ S'.a • ((S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g) * S.A.map (BK.hf g)) := by
  first | exact @GlobalTheory.BSP.strat_homDefect_φ | exact GlobalTheory.BSP.strat_homDefect_φ | (intros; apply GlobalTheory.BSP.strat_homDefect_φ <;> assumption)
end

