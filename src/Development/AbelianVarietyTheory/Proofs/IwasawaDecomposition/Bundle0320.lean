module

public import Mathlib
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0310
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0004
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerReindexComplexPlace
section
open Polynomial

noncomputable section

namespace GlobalTheory.TeichAt

open Formalism.L2.NT GlobalTheory.ParRay

theorem orderOf_coprime {g : ℕ} [hg : Fact g.Prime] {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) : (orderOf x).Coprime g := by
  have hpos := (isOfFinOrder_fbar hx).orderOf_pos
  set n := orderOf x with hn
  refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hg.out).2 ?_))
  intro hdvd
  have hm : g ^ n.factorization g * (n / g ^ n.factorization g) = n := Nat.ordProj_mul_ordCompl_eq_self n g
  have h1 : x ^ (g ^ n.factorization g * (n / g ^ n.factorization g)) = 1 := by rw [hm, hn, pow_orderOf_eq_one]
  have h2 : x ^ (n / g ^ n.factorization g) = 1 := pow_eq_one_of_charP g x _ _ h1
  have h3 : n ∣ n / g ^ n.factorization g := orderOf_dvd_of_pow_eq_one h2
  exact Nat.not_dvd_ordCompl hg.out hpos.ne' (hdvd.trans h3)

theorem map_zero_of_inj {Ω : Type} [Field Ω] {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* Ω)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  have h : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
  by_contra h0
  have h1 : t 0 = 1 := (mul_eq_left₀ h0).1 h
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  apply hx.2
  refine ht x 1 hx.1 one_ne_zero ?_
  have : t x = t x * t 0 := by rw [h1, mul_one]
  rw [this, ← map_mul, mul_zero, h1, map_one]

theorem exists_teich_reindex : ∀ (g : ℕ) [Fact g.Prime] (A : ValuationSubring ℂ)
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ),
    (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ t₀ : Formalism.CyclotomicNorms.Fbar g →* ℂ,
      Formalism.L2.NT.IsTeich A κ t₀ ∧ ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t₀ x = t₀ y → x = y := by
  intro g _ A κ t ht
  set s := redHom A κ t with hs_def
  have hs : ∀ x, s x = redThrough A κ (t x) := fun x => rfl
  have ht0 : t 0 = 0 := map_zero_of_inj t ht
  have hs0 : s 0 = 0 := by
    rw [hs, ht0]; unfold redThrough; rw [dite_eq_left (zero_mem A)]
    have : (⟨0, zero_mem A⟩ : A) = 0 := rfl
    rw [this, map_zero, map_zero]
  have hsne : ∀ x, x ≠ 0 → s x ≠ 0 := by
    intro x hx h0
    have hpos := (isOfFinOrder_fbar hx).orderOf_pos
    have : s x ^ orderOf x = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [h0, zero_pow hpos.ne'] at this
    exact zero_ne_one this
  have hinj : Function.Injective s := by
    intro x y h
    rcases eq_or_ne x 0 with rfl | hx
    · rcases eq_or_ne y 0 with rfl | hy
      · rfl
      · exact absurd (h.symm.trans hs0) (hsne y hy)
    · rcases eq_or_ne y 0 with rfl | hy
      · exact absurd (h.trans hs0) (hsne x hx)
      · exact redHom_inj A κ t ht x y hx hy (orderOf_coprime hx) (orderOf_coprime hy) h
  have hsurj : Function.Surjective s := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, hs0⟩
    have hn := (isOfFinOrder_fbar hy).orderOf_pos
    set n := orderOf y
    have hmem : ∀ z : Formalism.CyclotomicNorms.Fbar g, z ∈ nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g) ↔ z ^ n = 1 :=
      fun z => mem_nthRootsFinset hn 1
    obtain ⟨a, -, ha⟩ := Finset.surj_on_of_inj_on_of_card_le (s := nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g))
      (t := nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g)) (fun a _ => s a)
      (fun a ha => (hmem _).2 (by rw [← map_pow, (hmem a).1 ha, map_one]))
      (fun a₁ a₂ _ _ h => hinj h) le_rfl y ((hmem y).2 (pow_orderOf_eq_one y))
    exact ⟨a, ha.symm⟩
  let e : Formalism.CyclotomicNorms.Fbar g ≃* Formalism.CyclotomicNorms.Fbar g := MulEquiv.ofBijective s ⟨hinj, hsurj⟩
  have he : ∀ x, e x = s x := fun x => rfl
  refine ⟨t.comp e.symm.toMonoidHom, ?_, ?_⟩
  · intro x
    refine ⟨mem_of_monoidHom A t _, ?_⟩
    have h1 : s (e.symm x) = x := by rw [← he, MulEquiv.apply_symm_apply]
    have h2 := hs (e.symm x)
    unfold redThrough at h2
    rw [dite_eq_left (mem_of_monoidHom A t _)] at h2
    exact h2.symm.trans h1
  · intro x y hx hy h
    have hx' : e.symm x ≠ 0 := fun h0 => hx (by rw [← e.apply_symm_apply x, h0, he, hs0])
    have hy' : e.symm y ≠ 0 := fun h0 => hy (by rw [← e.apply_symm_apply y, h0, he, hs0])
    exact e.symm.injective (ht _ _ hx' hy' h)

end GlobalTheory.TeichAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePrimitiveRoot
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
namespace GlobalTheory.CycLayers

theorem layer_of_clauses {F : Type*} [NormedField F] (A R : Subring F) (h : A ≤ R) (l m : ℕ)
    (hlnorm : ‖(l : F)‖ < 1) (hl0 : (l : F) ≠ 0) (hm : 0 < m)
    (hdiv : ∀ x ∈ R, ∀ y ∈ R, ‖x‖ ≤ ‖y‖ → x / y ∈ R)
    (T : Finset F) (hT : ∀ x, x ∈ R ↔ x ∈ Submodule.span A (T : Set F))
    (ζ : F) (hzmem : ζ ∈ R) (hζ : IsPrimitiveRoot ζ m)
    (hlast : ∀ x ∈ R, ∃ (p : Polynomial A) (d : A), d ≠ 0 ∧ x * (d : F) = Polynomial.aeval ζ p) :
    letI := (Subring.inclusion h).toAlgebra;
    Module.Finite A R ∧ ∃ z : Rˣ, IsPrimitiveRoot (z : R) m ∧ ∀ x : FractionRing R, ∃ p : Polynomial A, ∃ d : A, d ≠ 0 ∧
      x * algebraMap _ (FractionRing R) (algebraMap _ R d) = algebraMap _ (FractionRing R) (Polynomial.aeval (z : R) p) := by
  let _ := (Subring.inclusion h).toAlgebra
  refine ⟨?_, ?_⟩
  · let f : R →ₗ[A] F :=
      { toFun := Subtype.val, map_add' := fun _ _ => rfl,
        map_smul' := fun a y => by rw [RingHom.id_apply, Algebra.smul_def, Subring.smul_def]; rfl }
    let S : Set R := Subtype.val ⁻¹' (T : Set F)
    have hS : S.Finite := T.finite_toSet.preimage Subtype.val_injective.injOn
    have himg : f '' S = (T : Set F) := by
      ext c
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hc
        have hcR : c ∈ R := (hT c).2 (Submodule.subset_span hc)
        exact ⟨⟨c, hcR⟩, hc, rfl⟩
    have key : ∀ y : R, y ∈ Submodule.span A S := by
      intro y
      have h1 : (y : F) ∈ Submodule.span A (T : Set F) := (hT y).1 y.2
      rw [← himg, ← Submodule.map_span] at h1
      obtain ⟨y', hy', hyy⟩ := h1
      have : y' = y := Subtype.ext hyy
      rw [← this]; exact hy'
    exact ⟨⟨hS.toFinset, by rw [Set.Finite.coe_toFinset]; exact eq_top_iff.2 fun y _ => key y⟩⟩
  · have hprim : IsPrimitiveRoot (⟨ζ, hzmem⟩ : R) m :=
      IsPrimitiveRoot.coe_submonoidClass_iff.1 hζ
    refine ⟨(hprim.isUnit hm.ne').unit, by simpa using hprim, ?_⟩
    intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
    set b : R := (s : R) with hbdef
    have hb : b ∈ nonZeroDivisors R := s.2
    have hb0 : (b : F) ≠ 0 := by
      intro h0
      have : b = 0 := Subtype.ext h0
      exact nonZeroDivisors.ne_zero hb this
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hb0) hlnorm
    have hlR : (l : F) ^ N ∈ R := pow_mem (natCast_mem R l) N
    have hlNA : (l : F) ^ N ∈ A := pow_mem (natCast_mem A l) N
    have hq : (l : F) ^ N / b ∈ R := by
      refine hdiv _ hlR _ b.2 ?_
      rw [norm_pow]; exact hN.le
    obtain ⟨p, d', hd', hpd⟩ := hlast _ (mul_mem a.2 hq)
    refine ⟨p, ⟨(l : F) ^ N, hlNA⟩ * d', ?_, ?_⟩
    · refine mul_ne_zero ?_ hd'
      intro h0
      have h1 : (l : F) ^ N = 0 := congrArg Subtype.val h0
      exact pow_ne_zero N hl0 h1
    · have hev : ((Polynomial.aeval ((hprim.isUnit hm.ne').unit : R) p : R) : F) = Polynomial.aeval ζ p := by
        rw [Polynomial.aeval_def, Polynomial.aeval_def, IsUnit.unit_spec]
        rw [show ((Polynomial.eval₂ (algebraMap A R) (⟨ζ, hzmem⟩ : R) p : R) : F) =
          R.subtype (Polynomial.eval₂ (algebraMap A R) (⟨ζ, hzmem⟩ : R) p) from rfl, Polynomial.hom_eval₂]
        rfl
      have hRd : algebraMap A R (⟨(l : F) ^ N, hlNA⟩ * d') =
          b * ⟨(l : F) ^ N / b, hq⟩ * algebraMap A R d' := by
        rw [map_mul]; congr 1
        apply Subtype.ext
        show (l : F) ^ N = (b : F) * ((l : F) ^ N / b)
        field_simp
      have hfin : a * ⟨(l : F) ^ N / b, hq⟩ * algebraMap A R d' =
          Polynomial.aeval ((hprim.isUnit hm.ne').unit : R) p := by
        apply Subtype.ext
        rw [hev, ← hpd]
        rfl
      rw [hRd, ← hfin, map_mul, map_mul, map_mul, map_mul, ← mul_assoc, ← mul_assoc, IsLocalization.mk'_spec]

theorem finite_primitive_root :
    ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ) (h : clC l (Kt l K₀ L) ≤ clC l (Kt l K₀ L ⊔ muK l k)), letI := (Subring.inclusion h).toAlgebra; Module.Finite ↥(clC l (Kt l K₀ L)) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧ ∃ z : (↥(clC l (Kt l K₀ L ⊔ muK l k)))ˣ, IsPrimitiveRoot (z : ↥(clC l (Kt l K₀ L ⊔ muK l k))) (l ^ k) ∧ ∀ x : FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), ∃ p : Polynomial ↥(clC l (Kt l K₀ L)), ∃ d : ↥(clC l (Kt l K₀ L)), d ≠ 0 ∧ x * algebraMap _ (FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k))) (algebraMap _ ↥(clC l (Kt l K₀ L ⊔ muK l k)) d) = algebraMap _ (FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k))) (Polynomial.aeval (z : ↥(clC l (Kt l K₀ L ⊔ muK l k))) p) := by
  intro l _ K₀ L k h
  obtain ⟨-, -, -, -, hdiv, -, ⟨T, hT⟩, ζ, hzmem, hζ, hlast⟩ := _root_.GlobalTheory.CycClosure.exists_cyclotomic_integers l K₀ L k
  have hlnorm : ‖(l : ℂ_[l])‖ < 1 := by
    have e : ((l : ℚ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by simp
    rw [← e, PadicComplex.norm_extends' l (l : ℚ_[l]), Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact layer_of_clauses _ _ h l (l ^ k) hlnorm hl0 (pow_pos (Fact.out : l.Prime).pos k) hdiv T hT ζ hzmem hζ hlast

end GlobalTheory.CycLayers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankJointEigenspaceCoefficientFieldComplex
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.PtLocalEig

theorem jointKer_fin_finrank {K C : Type} [Field K] [Field C] (φ : K →+* C) {ι : Type} [Fintype ι] {G : Type}
    (Mg : G → Matrix ι ι K) (s : Finset G) :
    Module.finrank K ↥(⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin (Mg g))) =
      Module.finrank C ↥(⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ))) := by
  classical
  let R : Matrix (↥s × ι) ι K := Matrix.of fun p b => Mg p.1.1 p.2 b
  have stack : ∀ {F : Type} [Field F] (N : G → Matrix ι ι F),
      (⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin (N g))) =
        LinearMap.ker (Matrix.mulVecLin (Matrix.of fun (p : ↥s × ι) b => N p.1.1 p.2 b)) := by
    intro F _ N
    ext c
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · intro h
      funext p
      have := congrFun (h p.1.1 p.1.2) p.2
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply] using this
    · intro h g hg
      funext a
      have := congrFun h (⟨g, hg⟩, a)
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply] using this
  have rn : ∀ {F : Type} [Field F] (N : Matrix (↥s × ι) ι F),
      N.rank + Module.finrank F (LinearMap.ker N.mulVecLin) = Fintype.card ι := by
    intro F _ N
    have := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    exact this
  have h1 := rn R
  have h2 := rn (R.map φ)
  rw [GlobalTheory.Core.Rk.rank_map_field] at h2
  rw [stack Mg, stack (fun g => (Mg g).map φ)]
  have e : (Matrix.of fun (p : ↥s × ι) b => ((Mg p.1.1).map φ) p.2 b) = R.map φ := by
    ext p b
    rfl
  rw [e]
  change Module.finrank K ↥(LinearMap.ker (Matrix.mulVecLin R)) = _
  omega

theorem jointKer_finrank {K C : Type} [Field K] [Field C] (φ : K →+* C) {ι : Type} [Fintype ι] {G : Type}
    (Mg : G → Matrix ι ι K) :
    Module.finrank K ↥(⨅ g, LinearMap.ker (Matrix.mulVecLin (Mg g))) =
      Module.finrank C ↥(⨅ g, LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ))) := by
  classical
  let kK : Finset G → Submodule K (ι → K) := fun s => ⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin (Mg g))
  let kC : Finset G → Submodule C (ι → C) := fun s => ⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ))
  have heq : ∀ s, Module.finrank K (kK s) = Module.finrank C (kC s) := fun s => jointKer_fin_finrank φ Mg s
  have hex : ∃ m, ∃ s : Finset G, Module.finrank K (kK s) = m := ⟨_, ∅, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hex
  have hmin : ∀ s' : Finset G, Module.finrank K (kK s) ≤ Module.finrank K (kK s') := fun s' =>
    hs ▸ Nat.find_min' hex ⟨s', rfl⟩
  have hminC : ∀ s' : Finset G, Module.finrank C (kC s) ≤ Module.finrank C (kC s') := fun s' => by
    rw [← heq, ← heq]; exact hmin s'
  have hK : (⨅ g, LinearMap.ker (Matrix.mulVecLin (Mg g))) = kK s := by
    apply le_antisymm
    · exact le_iInf₂ fun g _ => iInf_le _ g
    · refine le_iInf fun g => ?_
      have hins : kK (insert g s) = LinearMap.ker (Matrix.mulVecLin (Mg g)) ⊓ kK s := by
        simp only [kK, Finset.iInf_insert]
      have hle : kK (insert g s) ≤ kK s := by rw [hins]; exact inf_le_right
      have h := Submodule.eq_of_le_of_finrank_le hle (hmin _)
      rw [← h, hins]
      exact inf_le_left
  have hC : (⨅ g, LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ))) = kC s := by
    apply le_antisymm
    · exact le_iInf₂ fun g _ => iInf_le _ g
    · refine le_iInf fun g => ?_
      have hins : kC (insert g s) = LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ)) ⊓ kC s := by
        simp only [kC, Finset.iInf_insert]
      have hle : kC (insert g s) ≤ kC s := by rw [hins]; exact inf_le_right
      have h := Submodule.eq_of_le_of_finrank_le hle (hminC _)
      rw [← h, hins]
      exact inf_le_left
  rw [hK, hC]
  exact heq s

end GlobalTheory.PtLocalEig

namespace GlobalTheory.PtLocalEig

theorem eig_dim : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (E : Submodule ℂ (D.what₂.Mt μ j)), (∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → ∀ (c : ℂ) (f f' : GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • NG.tN (M μ j h1 h2).J s ϖ k f + NG.tN (M μ j h1 h2).J s ϖ k f') → (∀ y, y ∈ E ↔ ∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → Module.finrank (FractionRing (B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k), Module.End.eigenspace (B.hK j w v k) (κ v k)) = Module.finrank ℂ E := by
  intro D M B j w μ h1 h2 hμ φ hφ κ E hex hadd hE
  subst hμ
  classical
  haveI := Formalism.L2.finite_chooseBasisIndex (D := D) j w
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hjb := D.what₂.jMt_basis (D.what₂.muTw w) j b
  let bC := Module.Basis.mk hjb.1 hjb.2.ge
  have hb := B.iV_basis j w b
  let bV := Module.Basis.mk hb.1 hb.2.ge
  have hbC : ∀ a, bC a = D.what₂.jMt (D.what₂.muTw w) j (b a) := fun a => by simp [bC]
  have hbV : ∀ a, bV a = B.iV j w (b a) := fun a => by simp [bV]
  have rC : ∀ x r, bC.repr (D.what₂.jMt (D.what₂.muTw w) j x) r = D.what₂.embLL (b.repr x r) :=
    fun x r => Formalism.L2.NCov.repr_transport D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j) b hjb.1 hjb.2 x r
  have rV : ∀ x r, bV.repr (B.iV j w x) r = B.ec j w (b.repr x r) :=
    fun x r => Formalism.L2.NCov.repr_transport (B.ec j w) (B.iV j w) b hb.1 hb.2 x r
  let A : PlE D.host → ℕ → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) D.what₂.LL :=
    fun v k => LinearMap.toMatrix b b (B.hL j w v k)
  let G := {p : PlE D.host × ℕ // Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) p.1 p.2}
  let Mg : G → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) (FractionRing (B.Oc j w)) :=
    fun g => (A g.1.1 g.1.2).map (B.ec j w) - κ g.1.1 g.1.2 • 1
  set Mw := M (D.what₂.muTw w) j h1 h2 with hMw

  have hV : ∀ v k (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k) c,
      B.hK j w v k (bV.equivFun.symm c) = κ v k • bV.equivFun.symm c ↔ Matrix.mulVec (Mg ⟨(v, k), hvk⟩) c = 0 := by
    intro v k hvk c
    have hmat : LinearMap.toMatrix bV bV (B.hK j w v k) = (A v k).map (B.ec j w) := by
      ext r c'
      rw [LinearMap.toMatrix_apply, Matrix.map_apply, hbV, B.hK_def, rV]
      simp only [A, LinearMap.toMatrix_apply]
    have hr := LinearMap.toMatrix_mulVec_repr bV bV (B.hK j w v k) (bV.equivFun.symm c)
    rw [hmat] at hr
    have hc : ⇑(bV.repr (bV.equivFun.symm c)) = c := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hc] at hr
    rw [← bV.equivFun.injective.eq_iff, map_smul, LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply, ← hr]
    simp only [Mg, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have hPV : (⨅ (v : PlE D.host) (k : ℕ) (_ : Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k),
      Module.End.eigenspace (B.hK j w v k) (κ v k)).map (bV.equivFun : B.V j w →ₗ[FractionRing (B.Oc j w)] _) =
      ⨅ g : G, LinearMap.ker (Matrix.mulVecLin (Mg g)) := by
    ext c
    rw [Submodule.mem_map_equiv]
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · rintro h ⟨⟨v, k⟩, hvk⟩
      exact (hV v k hvk c).1 (h v k hvk)
    · intro h v k hvk
      exact (hV v k hvk c).2 (h ⟨⟨v, k⟩, hvk⟩)

  have hCk : ∀ v k (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k) (y : D.what₂.Mt (D.what₂.muTw w) j),
      (∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
        IsConjPl D.host v s.w → Formalism.AUTREP.IsUnif D.host.E s.v ϖ →
        Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real y) = φ (κ v k) • Mw.real y) ↔
      Matrix.mulVec ((Mg ⟨(v, k), hvk⟩).map φ) (bC.equivFun y) = 0 := by
    intro v k hvk y
    obtain ⟨s0, ϖ0, hc0, hu0⟩ := hex v k hvk
    let tC : Module.End ℂ (D.what₂.Mt (D.what₂.muTw w) j) :=
      bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))
    have hagree : ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
        IsConjPl D.host v s.w → Formalism.AUTREP.IsUnif D.host.E s.v ϖ →
        ∀ x, Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real x) = Mw.real (tC x) := by
      intro s ϖ hc hu
      have hadd' := hadd v k s ϖ hvk hc hu
      have htN0 : Formalism.L2.NG.tN Mw.J s ϖ k (0 : Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W) = 0 := by
        have := hadd' 1 0 0
        rw [one_smul, add_zero, one_smul] at this
        simpa using this
      let Lt : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] (Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W) :=
        { toFun := fun y => Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real y)
          map_add' := fun y y' => by
            have := hadd' 1 (Mw.real y) (Mw.real y')
            rw [one_smul, one_smul] at this
            simp only [map_add (f := _)]
            exact this
          map_smul' := fun c y => by
            have := hadd' c (Mw.real y) 0
            rw [add_zero, htN0, add_zero] at this
            simp only [map_smul, RingHom.id_apply]
            exact this }
      have hLt : Lt = Mw.real.comp tC := bC.ext fun a => by
        have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) a
        show Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real (bC a)) =
          Mw.real ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC a))
        rw [e, hbC a]
        exact (B.hL_def j w h1 h2 v k s ϖ hvk hc hu (b a)).symm
      intro x
      exact LinearMap.congr_fun hLt x
    have hmat : LinearMap.toMatrix bC bC tC = (A v k).map D.what₂.embLL := by
      ext r c
      rw [LinearMap.toMatrix_apply, Matrix.map_apply]
      have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) c
      show bC.repr ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC c)) r = _
      rw [e, rC]
      simp only [A, LinearMap.toMatrix_apply]
    have hMg : (Mg ⟨(v, k), hvk⟩).map φ = (A v k).map D.what₂.embLL - φ (κ v k) • 1 := by
      ext r c
      simp only [Mg, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp [hφ]
    have hvec : tC y = φ (κ v k) • y ↔ Matrix.mulVec ((Mg ⟨(v, k), hvk⟩).map φ) (bC.equivFun y) = 0 := by
      rw [hMg, Matrix.sub_mulVec, ← hmat, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero,
        Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr, ← Finsupp.coe_smul, ← map_smul]
      exact ⟨fun h => by rw [h], fun h => bC.repr.injective (DFunLike.coe_injective h)⟩
    constructor
    · intro h
      apply hvec.1
      apply Mw.real_inj
      rw [← hagree s0 ϖ0 hc0 hu0, h s0 ϖ0 hc0 hu0, map_smul]
    · intro h s ϖ hc hu
      rw [hagree s ϖ hc hu, hvec.2 h, map_smul]
  have hPC : E.map (bC.equivFun : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] _) =
      ⨅ g : G, LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ)) := by
    ext d
    rw [Submodule.mem_map_equiv, hE]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · rintro h ⟨⟨v, k⟩, hvk⟩
      have := (hCk v k hvk (bC.equivFun.symm d)).1 (fun s ϖ hc hu => h v k s ϖ hvk hc hu)
      rwa [LinearEquiv.apply_symm_apply] at this
    · intro h v k s ϖ hvk hc hu
      refine (hCk v k hvk _).2 ?_ s ϖ hc hu
      rw [LinearEquiv.apply_symm_apply]
      exact h ⟨⟨v, k⟩, hvk⟩
  rw [← LinearEquiv.finrank_map_eq bV.equivFun, hPV, ← LinearEquiv.finrank_map_eq bC.equivFun E, hPC]
  exact jointKer_finrank φ Mg

end GlobalTheory.PtLocalEig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
section
noncomputable section

open NumberField IsDedekindDomain Formalism.AUTREP Formalism.UG ReciprocityTheory.Aut

namespace GlobalTheory.SatInd

section Field

variable {K : Type} [Field K]

theorem antiJ_map (g : K →+* K) (n : ℕ) : (antiJ K n).map g = antiJ K n := by
  ext i j
  simp only [antiJ, Matrix.map_apply]
  split_ifs <;> simp

theorem cT_map (g σ σ' : K →+* K) (hg : ∀ x, g (σ x) = σ' (g x)) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) : cT σ' (M.map g) = (cT σ M).map g := by
  ext i j
  simp [cT, hg]

def guMap (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)) (n : ℕ) :
    GU σ n →* GU σ' n :=
  ((bc (n := Fin n) (g : K →+* K)).comp (GU σ n).subtype).codRestrict (GU σ' n) (fun y => by
    have hy : cT σ ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * antiJ K n *
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = antiJ K n := y.2
    show cT σ' (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (g : K →+* K)) * antiJ K n *
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (g : K →+* K) = antiJ K n
    rw [cT_map (g : K →+* K) σ σ' hg, ← antiJ_map (g : K →+* K) n]
    rw [← Matrix.map_mul, ← Matrix.map_mul, hy])

theorem guMap_val (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)) {n : ℕ}
    (y : GU σ n) :
    (((guMap g hg n y : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map g := rfl

end Field

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

def gEquiv (D D' : InertDatum L n v w) : w.adicCompletion L ≃+* w.adicCompletion L :=
  D.e.symm.trans D'.e

theorem gEquiv_e (D D' : InertDatum L n v w) (y) : gEquiv D D' (D.e y) = D'.e y := by
  simp [gEquiv]

theorem gEquiv_comm (D D' : InertDatum L n v w) :
    ∀ x, gEquiv D D' (D.σw x) = D'.σw (gEquiv D D' x) := by
  intro x
  obtain ⟨y, rfl⟩ := D.e.surjective x
  rw [← D.comm, gEquiv_e, gEquiv_e, D'.comm]

theorem gEquiv_intL (D D' : InertDatum L n v w) :
    ∀ x, x ∈ intL (w.adicCompletion L) ↔ gEquiv D D' x ∈ intL (w.adicCompletion L) := by
  intro x
  obtain ⟨y, rfl⟩ := D.e.surjective x
  rw [gEquiv_e, ← D.integ, ← D'.integ]

end GlobalTheory.SatInd
end
end

