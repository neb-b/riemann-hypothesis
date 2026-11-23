module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusKernelHopfLePowCotangent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobKerOrder

theorem finrank_le_pow_of_aeval_surjective {n d : ℕ} {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] (x : Fin d → A) (hsurj : Function.Surjective (MvPolynomial.aeval (R := K) x))
    (hpow : ∀ i, x i ^ n = 0) :
    Module.finrank K A ≤ n ^ d := by
  classical
  let e : (Fin d → Fin n) → (Fin d →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm fun i => a i
  let v : (Fin d → Fin n) → A := fun a => MvPolynomial.aeval (R := K) x (MvPolynomial.monomial (e a) 1)
  have hmono : ∀ m : Fin d →₀ ℕ,
      MvPolynomial.aeval (R := K) x (MvPolynomial.monomial m 1) ∈ Submodule.span K (Set.range v) := by
    intro m
    by_cases hm : ∀ i, m i < n
    · refine Submodule.subset_span ⟨fun i => ⟨m i, hm i⟩, ?_⟩
      have : e (fun i => ⟨m i, hm i⟩) = m := by
        ext i; simp [e]
      simp only [v, this]
    · push_neg at hm
      obtain ⟨i, hi⟩ := hm
      have h0 : MvPolynomial.aeval (R := K) x (MvPolynomial.monomial m 1) = 0 := by
        rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod]
        by_cases hmi : m i = 0
        · have hn : n = 0 := by omega
          subst hn
          have h10 : (1 : A) = 0 := by simpa using hpow i
          rw [← mul_one (∏ j ∈ m.support, x j ^ m j), h10, mul_zero]
        · apply Finset.prod_eq_zero (i := i) (by simpa using hmi)
          obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hi
          rw [hr, pow_add, hpow i, zero_mul]
      rw [h0]; exact Submodule.zero_mem _
  have htop : Submodule.span K (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨P, rfl⟩ := hsurj y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [P.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    have : MvPolynomial.monomial m (AddMonoidAlgebra.coeff P m) =
        AddMonoidAlgebra.coeff P m • MvPolynomial.monomial m (1 : K) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (hmono m)
  have h1 := finrank_range_le_card (R := K) v
  rw [Set.finrank, htop, finrank_top] at h1
  simpa using h1

theorem finrank_le_pow_finrank_cot (p : ℕ) [hp : Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [Module.Finite K H] :
    Module.finrank K (H ⧸ frobKerIdeal p K H) ≤ p ^ Module.finrank K (Cot K H) := by
  classical
  set J := frobKerIdeal p K H with hJ
  set ε := Bialgebra.counitAlgHom K H with hε
  set mk := Ideal.Quotient.mkₐ K J with hmk
  have hJI : ∀ a ∈ J, ε a = 0 := fun a ha => frobKerIdeal_le_augIdeal hp.out.ne_zero K H ha
  set εQ : (H ⧸ J) →ₐ[K] K := Ideal.Quotient.liftₐ J ε hJI with hεQ
  have hεQmk : ∀ a, εQ (mk a) = ε a := fun a => rfl
  have hmks : Function.Surjective mk := Ideal.Quotient.mkₐ_surjective K J
  haveI hfinQ : Module.Finite K (H ⧸ J) := Module.Finite.of_surjective mk.toLinearMap hmks
  haveI : IsNoetherianRing (H ⧸ J) := isNoetherian_of_tower K inferInstance

  have hkerQ : ∀ z ∈ RingHom.ker εQ, ∃ a ∈ RingHom.ker ε, mk a = z := by
    intro z hz
    obtain ⟨a, rfl⟩ := hmks z
    refine ⟨a, ?_, rfl⟩
    rw [RingHom.mem_ker] at hz ⊢
    rw [← hεQmk]; exact hz
  have hpowQ : ∀ z ∈ RingHom.ker εQ, z ^ p = 0 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hkerQ z hz
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
  have hnil : IsNilpotent (RingHom.ker εQ) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨p, hpowQ f hf⟩

  haveI : Module.Finite K (AugCot ε) := Module.Finite.of_surjective _ (AugCot.d_surjective ε)
  set d := Module.finrank K (AugCot ε) with hd
  let b := Module.finBasis K (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  have hsum : ∀ l : Fin d → K, AugCot.d ε (∑ i, l i • (x i : H)) = ∑ i, l i • b i := by
    intro l
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hx]
  have hmem : ∀ l : Fin d → K, (∑ i, l i • (x i : H)) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (x i).2
  have hspanH : ∀ a ∈ RingHom.ker ε, ∃ l : Fin d → K, a - ∑ i, l i • (x i : H) ∈ RingHom.ker ε ^ 2 := by
    intro a ha
    refine ⟨b.repr (AugCot.d ε a), ?_⟩
    have h1 : AugCot.d ε (a - ∑ i, b.repr (AugCot.d ε a) i • (x i : H)) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem ha (hmem _)), Ideal.toCotangent_eq_zero] at h1
  let y : Fin d → H ⧸ J := fun i => mk (x i)
  have hy : ∀ i, y i ∈ RingHom.ker εQ := fun i => by
    rw [RingHom.mem_ker, hεQmk]; exact (x i).2
  have hmapI : Ideal.map mk (RingHom.ker ε) ≤ RingHom.ker εQ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact ha
  have hspan : ∀ z ∈ RingHom.ker εQ, ∃ l : Fin d → K, z - ∑ i, l i • y i ∈ RingHom.ker εQ ^ 2 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hkerQ z hz
    obtain ⟨l, hl⟩ := hspanH a ha
    refine ⟨l, ?_⟩
    have h1 : mk (a - ∑ i, l i • (x i : H)) ∈ Ideal.map mk (RingHom.ker ε ^ 2) :=
      Ideal.mem_map_of_mem _ hl
    rw [Ideal.map_pow] at h1
    have h2 := Ideal.pow_right_mono hmapI 2 h1
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [y, map_sub, map_sum, map_smul] using h2
  have hsurj := GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent εQ hnil y hy hspan
  have hyq : ∀ i, y i ^ p = 0 := fun i => hpowQ _ (hy i)

  exact finrank_le_pow_of_aeval_surjective y hsurj hyq

end GlobalTheory.PDiv.FrobKerOrder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderDeformationPointsDifferEpsAllOpens
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS.EpsDiff

open GlobalTheory.FlagMod (ev_spMap spMap_ev tau tau_le le_preimage_comp le_preimage_map)

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

variable {B : Type} [CommRing B]

abbrev mkE (ε : B) : B →+* B ⧸ Ideal.span {ε} := Ideal.Quotient.mk _

def FR (ε : B) : Subring (B × DualNumber (B ⧸ Ideal.span {ε})) :=
  RingHom.eqLocus ((mkE ε).comp (RingHom.fst _ _))
    ((TrivSqZeroExt.fstHom (B ⧸ Ideal.span {ε}) _ _).toRingHom.comp (RingHom.snd _ _))

def p1 (ε : B) : FR ε →+* B := (RingHom.fst _ _).comp (FR ε).subtype

def p2 (ε : B) : FR ε →+* DualNumber (B ⧸ Ideal.span {ε}) := (RingHom.snd _ _).comp (FR ε).subtype

theorem FR_ext {ε : B} {r s : FR ε} (h1 : p1 ε r = p1 ε s) (h2 : p2 ε r = p2 ε s) : r = s :=
  Subtype.ext (Prod.ext h1 h2)

theorem epsFibreProduct_quotient_fst_eq_dual_fst {ε : B} (r : FR ε) : mkE ε (p1 ε r) = (p2 ε r).fst := r.2

def liftFR {ε : B} {C : Type} [CommRing C] (a : C →+* B) (b : C →+* DualNumber (B ⧸ Ideal.span {ε}))
    (h : ∀ c, mkE ε (a c) = (b c).fst) : C →+* FR ε := (a.prod b).codRestrict (FR ε) h

theorem exists_liftFR {ε : B} {C : Type} [CommRing C] (a : C →+* B) (b : C →+* DualNumber (B ⧸ Ideal.span {ε}))
    (h : ∀ c, mkE ε (a c) = (b c).fst) : ∃ q : C →+* FR ε, (p1 ε).comp q = a ∧ (p2 ε).comp q = b :=
  ⟨liftFR a b h, rfl, rfl⟩

def mulE {ε : B} (hε : ε * ε = 0) : (B ⧸ Ideal.span {ε}) →ₗ[B] B :=
  Submodule.liftQ _ (LinearMap.mul B B ε) (by
    intro c hc
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hc
    simp only [LinearMap.mem_ker, LinearMap.mul_apply']
    rw [← _root_.mul_assoc, _root_.mul_comm ε d, _root_.mul_assoc, hε, MulZeroClass.mul_zero])

theorem mulE_mk {ε : B} (hε : ε * ε = 0) (c : B) : mulE hε (mkE ε c) = ε * c := rfl

def sg {ε : B} (hε : ε * ε = 0) : FR ε →+* B where
  toFun r := p1 ε r + mulE hε (p2 ε r).snd
  map_one' := by simp
  map_zero' := by simp
  map_add' r s := by
    rw [(p1 ε).map_add, (p2 ε).map_add, TrivSqZeroExt.snd_add, (mulE hε).map_add]
    ring
  map_mul' r s := by
    obtain ⟨c, hc⟩ : ∃ c, mkE ε c = (p2 ε r).snd := Ideal.Quotient.mk_surjective _
    obtain ⟨d, hd⟩ : ∃ d, mkE ε d = (p2 ε s).snd := Ideal.Quotient.mk_surjective _
    have e : (p2 ε (r * s)).snd = mkE ε (p1 ε r * d + c * p1 ε s) := by
      rw [map_mul, DualNumber.snd_mul, map_add (f := _), map_mul, map_mul, hc, hd, epsFibreProduct_quotient_fst_eq_dual_fst, epsFibreProduct_quotient_fst_eq_dual_fst]
    rw [e, ← hc, ← hd, map_mul, mulE_mk, mulE_mk, mulE_mk]
    linear_combination (-(c * d)) * hε

theorem sg_apply {ε : B} (hε : ε * ε = 0) (r : FR ε) : sg hε r = p1 ε r + mulE hε (p2 ε r).snd := rfl

theorem epsFibreProductSnd_surjective (ε : B) : Function.Surjective (p2 ε) := by
  intro w
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective w.fst
  exact ⟨⟨(b, w), hb⟩, rfl⟩

theorem specMap_epsFibreProductSnd_surjective {ε : B} (hε : ε * ε = 0) : Function.Surjective (spMap (p2 ε)) := by
  intro q
  have hk : RingHom.ker (p2 ε) ≤ q.asIdeal := by
    intro r hr
    have hr' : p2 ε r = 0 := hr
    refine q.isPrime.mem_of_pow_mem 2 ?_
    have h1 : mkE ε (p1 ε r) = 0 := by rw [epsFibreProduct_quotient_fst_eq_dual_fst, hr']; rfl
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    have : r ^ 2 = 0 := by
      apply FR_ext
      · rw [map_pow, ← hd, map_zero]
        linear_combination (d * d) * hε
      · rw [map_pow, hr', map_zero]; simp
    rw [this]; exact zero_mem _
  have := _root_.range_comap_of_surjective _ (p2 ε) (epsFibreProductSnd_surjective ε)
  have hq : q ∈ Set.range (PrimeSpectrum.comap (p2 ε)) := by
    rw [this]; exact hk
  exact hq

theorem top_le_preimage_of_epsFibreSnd_comp {ε : B} (hε : ε * ε = 0) {Y : Scheme.{0}} {T : Sp (FR ε) ⟶ Y} {O : Y.Opens}
    (h : ⊤ ≤ (spMap (p2 ε) ≫ T) ⁻¹ᵁ O) : ⊤ ≤ T ⁻¹ᵁ O := by
  intro p _
  obtain ⟨q, rfl⟩ := specMap_epsFibreProductSnd_surjective hε p
  exact h (Set.mem_univ q)

theorem pt_ext {ε : B} {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {a b : Sp (FR ε) ⟶ Y}
    (ha : ⊤ ≤ a ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ U) (h1 : spMap (p1 ε) ≫ a = spMap (p1 ε) ≫ b)
    (h2 : spMap (p2 ε) ≫ a = spMap (p2 ε) ≫ b) : a = b := by
  have e1 := GlobalTheory.FlagMod.ev_congr h1 U (le_preimage_comp _ ha) (le_preimage_comp _ hb)
  have e2 := GlobalTheory.FlagMod.ev_congr h2 U (le_preimage_comp _ ha) (le_preimage_comp _ hb)
  rw [ev_spMap _ _ _ ha, ev_spMap _ _ _ hb] at e1 e2
  have e : ev a U ha = ev b U hb := RingHom.ext fun f =>
    FR_ext (RingHom.congr_fun e1 f) (RingHom.congr_fun e2 f)
  rw [← spMap_ev a hU ha, ← spMap_ev b hU hb, e]

end GlobalTheory.CechKS.EpsDiff

namespace GlobalTheory.CechKS

open EpsDiff
open GlobalTheory.FlagMod (ev_spMap spMap_ev tau tau_le le_preimage_comp le_preimage_map)

theorem valR_sub_eq_eps_mul_of_affine : ∀ {K : Type} [Field K] {A : Over (Sp K)} {A' : Over (Sp (DualNumber K))} {i : A.left ⟶ A'.left} (hi : i ≫ A'.hom = A.hom ≫ GlobalTheory.DeRham.epsRed K) {X Z : Scheme.{0}} {h : Z ⟶ X} {y1 : Sp (DualNumber K) ⟶ X} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} (hm' : IsPullback m' A'.hom h y1) (him : i ≫ m' = m) (U : X.affineOpens) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1) (Ω : Z.affineOpens) (hΩ : Ω.1 ≤ h ⁻¹ᵁ U.1) {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1)) (S : Sp (DualNumber B) ⟶ A.left) (hS : S ≫ A.hom = spMap ((algebraMap B (DualNumber B)).comp (baseMap K B))) (hSx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ S = x) (l₁ l₂ : Sp B ⟶ A'.left) (hl₁ : l₁ ≫ A'.hom = spMap (algebraMap (DualNumber K) B)) (hl₂ : l₂ ≫ A'.hom = spMap (algebraMap (DualNumber K) B)) (hΩ₁ : ⊤ ≤ (l₁ ≫ m') ⁻¹ᵁ Ω.1) (hΩ₂ : ⊤ ≤ (l₂ ≫ m') ⁻¹ᵁ Ω.1) (h₂ : ∀ f, ∃ c : B, valR (l₂ ≫ m') Ω.1 f = valR (x ≫ m) Ω.1 f + algebraMap (DualNumber K) B DualNumber.eps * c) (h₁₂ : ∀ f, valR (l₁ ≫ m') Ω.1 f - valR (l₂ ≫ m') Ω.1 f = algebraMap (DualNumber K) B DualNumber.eps * (valR (S ≫ m) Ω.1 f).snd) (O : A'.left.Opens) (hxO : ⊤ ≤ x ⁻¹ᵁ (i ⁻¹ᵁ O)) (f : Γ(A'.left, O)), valR l₁ O f - valR l₂ O f = algebraMap (DualNumber K) B DualNumber.eps * (valR S (i ⁻¹ᵁ O) ((i.app O).hom f)).snd := by
  intro K _ A A' i hi X Z h y1 m m' hm' him U hU' Ω hΩ B _ _ x hxΩ S hS hSx l₁ l₂ hl₁ hl₂ hΩ₁ hΩ₂ h₂ h₁₂ O hxO f
  set ε : B := algebraMap (DualNumber K) B DualNumber.eps with hεd
  have hε : ε * ε = 0 := by rw [hεd, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hmkε : mkE ε ε = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ε)
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω.1 := hxΩ
  have hSxm : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ S ≫ m = x ≫ m := by rw [← Category.assoc, hSx]
  have hSm : ⊤ ≤ (S ≫ m) ⁻¹ᵁ Ω.1 := le_preimage_of_red hSxm hxm
  have hSO : ⊤ ≤ S ⁻¹ᵁ (i ⁻¹ᵁ O) := le_preimage_of_red hSx hxO
  have hfst : ∀ g, (ev (S ≫ m) Ω.1 hSm g).fst = ev (x ≫ m) Ω.1 hxm g := fun g => by
    rw [GlobalTheory.FlagMod.ev_congr hSxm.symm Ω.1 hxm (le_preimage_comp _ hSm), ev_spMap _ _ _ hSm]
    rfl
  obtain ⟨q, hqa, hqb⟩ := exists_liftFR (ev (l₂ ≫ m') Ω.1 hΩ₂) ((dualMap (mkE ε)).comp (ev (S ≫ m) Ω.1 hSm))
    (fun g => by
      obtain ⟨c, hc⟩ := h₂ g
      rw [valR_eq_ev _ _ hΩ₂, valR_eq_ev _ _ hxm] at hc
      rw [hc, map_add (f := _), map_mul, hmkε, MulZeroClass.zero_mul, add_zero, ← hfst]
      simp [dualMap])
  let j2 : DualNumber K →+* DualNumber (B ⧸ Ideal.span {ε}) :=
    ((dualMap (mkE ε)).comp ((algebraMap B (DualNumber B)).comp (baseMap K B))).comp
      (TrivSqZeroExt.fstHom K K K).toRingHom
  have hj2 : ∀ a, j2 a = TrivSqZeroExt.inl (mkE ε (baseMap K B a.fst)) := fun a => by
    ext <;> simp [j2, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  obtain ⟨j, hja, hjb⟩ := exists_liftFR (algebraMap (DualNumber K) B) j2 (fun a => by
    have ha : a = algebraMap K (DualNumber K) a.fst + DualNumber.eps * algebraMap K (DualNumber K) a.snd := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [hj2, TrivSqZeroExt.fst_inl]
    conv_lhs => rw [ha]
    rw [map_add (f := _), map_mul, ← hεd, map_add (f := _), map_mul, hmkε, MulZeroClass.zero_mul, add_zero]
    rfl)
  have b1 : spMap (p1 ε) ≫ spMap j = l₂ ≫ A'.hom := by rw [spc, hl₂, hja]
  have b2 : spMap (p2 ε) ≫ spMap j = (spMap (dualMap (mkE ε)) ≫ S ≫ i) ≫ A'.hom := by
    rw [Category.assoc, Category.assoc, hi, ← Category.assoc S, hS, ← Category.assoc, spc, spc]
    rw [hjb]
    exact (spc (TrivSqZeroExt.fstHom K K K).toRingHom
      ((dualMap (mkE ε)).comp ((algebraMap B (DualNumber B)).comp (baseMap K B)))).symm
  have b3 : spMap (sg hε) ≫ spMap j = l₁ ≫ A'.hom := by
    rw [spc, hl₁]
    refine congrArg spMap (RingHom.ext fun a => ?_)
    have e1 : p1 ε (j a) = algebraMap (DualNumber K) B a := RingHom.congr_fun hja a
    have e2 : p2 ε (j a) = j2 a := RingHom.congr_fun hjb a
    rw [RingHom.comp_apply, sg_apply, e1, e2, hj2, TrivSqZeroExt.snd_inl, map_zero, add_zero]
  have z1 : spMap (p1 ε) ≫ spMap q ≫ tau Ω.2 = l₂ ≫ m' := by
    rw [← Category.assoc, spc, hqa]
    exact spMap_ev _ Ω.2 hΩ₂
  have z2 : spMap (p2 ε) ≫ spMap q ≫ tau Ω.2 = (spMap (dualMap (mkE ε)) ≫ S ≫ i) ≫ m' := by
    rw [Category.assoc, Category.assoc, him, ← Category.assoc, spc, hqb, ← spc, Category.assoc]
    exact congrArg _ (spMap_ev (S ≫ m) Ω.2 hSm)
  have z3 : spMap (sg hε) ≫ spMap q ≫ tau Ω.2 = l₁ ≫ m' := by
    rw [← Category.assoc, spc]
    have : (sg hε).comp q = ev (l₁ ≫ m') Ω.1 hΩ₁ := by
      refine RingHom.ext fun g => ?_
      have e := h₁₂ g
      rw [valR_eq_ev _ _ hΩ₂, valR_eq_ev _ _ hΩ₁, valR_eq_ev _ _ hSm] at e
      have e' : (dualMap (mkE ε) (ev (S ≫ m) Ω.1 hSm g)).snd = mkE ε (ev (S ≫ m) Ω.1 hSm g).snd := by
        simp [dualMap]
      have e1 : p1 ε (q g) = ev (l₂ ≫ m') Ω.1 hΩ₂ g := RingHom.congr_fun hqa g
      have e2 : p2 ε (q g) = dualMap (mkE ε) (ev (S ≫ m) Ω.1 hSm g) := RingHom.congr_fun hqb g
      rw [RingHom.comp_apply, sg_apply, e1, e2, e', mulE_mk, ← e]
      ring
    rw [this]
    exact spMap_ev _ Ω.2 hΩ₁
  have hw : (spMap q ≫ tau Ω.2) ≫ h = spMap j ≫ y1 := by
    refine pt_ext U.2 (le_preimage_map h hΩ (le_preimage_comp _ (tau_le Ω.2 le_rfl))) (le_preimage_comp _ hU') ?_ ?_
    · rw [← Category.assoc, z1, ← Category.assoc, b1, Category.assoc, Category.assoc, hm'.w]
    · rw [← Category.assoc, z2, ← Category.assoc (spMap (p2 ε)), b2, Category.assoc _ m', Category.assoc _ A'.hom,
        hm'.w]
  obtain ⟨T, T1, T2⟩ : ∃ T : Sp (FR ε) ⟶ A'.left, T ≫ m' = spMap q ≫ tau Ω.2 ∧ T ≫ A'.hom = spMap j :=
    ⟨hm'.lift _ _ hw, hm'.lift_fst _ _ hw, hm'.lift_snd _ _ hw⟩
  have t1 : spMap (p1 ε) ≫ T = l₂ :=
    hm'.hom_ext (by rw [Category.assoc, T1, z1]) (by rw [Category.assoc, T2, b1])
  have t2 : spMap (p2 ε) ≫ T = spMap (dualMap (mkE ε)) ≫ S ≫ i :=
    hm'.hom_ext (by rw [Category.assoc, T1, z2]) (by rw [Category.assoc, T2, b2])
  have t3 : spMap (sg hε) ≫ T = l₁ :=
    hm'.hom_ext (by rw [Category.assoc, T1, z3]) (by rw [Category.assoc, T2, b3])
  have hSi : ⊤ ≤ (S ≫ i) ⁻¹ᵁ O := hSO
  have hT : ⊤ ≤ T ⁻¹ᵁ O := top_le_preimage_of_epsFibreSnd_comp hε (by rw [t2]; exact le_preimage_comp _ hSi)
  have v2 := GlobalTheory.FlagMod.ev_congr t2 O (le_preimage_comp _ hT) (le_preimage_comp _ hSi)
  rw [ev_spMap _ _ _ hT, ev_spMap _ _ _ hSi] at v2
  have v2' : p2 ε (ev T O hT f) = dualMap (mkE ε) (ev (S ≫ i) O hSi f) := RingHom.congr_fun v2 f
  have e' : (dualMap (mkE ε) (ev (S ≫ i) O hSi f)).snd = mkE ε (ev (S ≫ i) O hSi f).snd := by
    simp [dualMap]
  rw [← valR_comp_app, valR_eq_ev _ _ hSi, ← t1, ← t3, valR_eq_ev _ _ (le_preimage_comp _ hT),
    valR_eq_ev _ _ (le_preimage_comp _ hT), ev_spMap _ _ _ hT, ev_spMap _ _ _ hT, RingHom.comp_apply,
    RingHom.comp_apply, sg_apply, v2', e', mulE_mk]
  ring

end GlobalTheory.CechKS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOpenPartGroupSchemeProductMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FlatMul

variable {T : Scheme.{0}}

theorem whiskerRight_pb {H V : Over T} (q : V ⟶ H) (Y : Over T) :
    IsPullback (pullback.fst V.hom Y.hom) (q ▷ Y).left q.left (pullback.fst H.hom Y.hom) := by
  refine (IsPullback.of_right (h₁₁ := (q ▷ Y).left) (v₁₁ := pullback.fst V.hom Y.hom)
    (h₂₁ := q.left) (v₁₂ := pullback.fst H.hom Y.hom) ?_ (Over.whiskerRight_left_fst q)
    (IsPullback.of_hasPullback H.hom Y.hom).flip).flip
  rw [Over.whiskerRight_left_snd, Over.w]
  exact (IsPullback.of_hasPullback V.hom Y.hom).flip

theorem whiskerLeft_pb (X : Over T) {A B : Over T} (q : A ⟶ B) :
    IsPullback (snd X A).left (X ◁ q).left q.left (snd X B).left := by
  have : IsPullback (snd X A) (X ◁ q) q (snd X B) := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.snd ≫ fst X B) s.fst)
      (fun s => by simp) (fun s => ?_) (fun s m h₁ h₂ => ?_)⟩⟩
    · ext1
      · simp
      · simp [s.condition]
    · ext1
      · simp [← h₂]
      · simp [← h₁]
  exact this.map (Over.forget T)

theorem isIso_shear (H : Over T) [GrpObj H] : IsIso (lift μ[H] (snd H H)) := by
  refine ⟨⟨lift (fst H H * (snd H H)⁻¹) (snd H H), ?_, ?_⟩⟩
  · have hμ : μ[H] = fst H H * snd H H := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    apply hom_ext
    · rw [Category.assoc, lift_fst, comp_mul, lift_fst, GrpObj.comp_inv, lift_snd, hμ, mul_inv_cancel_right,
        Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]
  · have hμ : μ[H] = fst H H * snd H H := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    apply hom_ext
    · rw [Category.assoc, lift_fst, hμ, comp_mul, lift_fst, lift_snd, inv_mul_cancel_right, Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]

theorem flat_mu (H : Over T) [GrpObj H] (hH : Flat H.hom) : Flat μ[H].left := by
  have e : μ[H] = lift μ[H] (snd H H) ≫ fst H H := by rw [lift_fst]
  have := isIso_shear H
  have : IsIso (lift μ[H] (snd H H)).left := (Over.forget T).map_isIso (lift μ[H] (snd H H))
  have hfst : Flat (fst H H).left := by
    have h1 : (fst H H).left = pullback.fst H.hom H.hom := by simp
    rw [h1]
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback H.hom H.hom).flip hH
  rw [e, Over.comp_left]
  infer_instance

theorem main : ∀ (T : Scheme.{0}) (H V : Over T) [GrpObj H] (e : V ⟶ H), IsOpenImmersion e.left → Flat H.hom →
    Flat ((fst V V ≫ e) * (snd V V ≫ e)).left := by
  intro T H V _ e he hH
  have h1 : Flat (e ▷ V).left := MorphismProperty.of_isPullback (whiskerRight_pb e V)
    (inferInstance : Flat e.left)
  have h2 : Flat (H ◁ e).left := MorphismProperty.of_isPullback (whiskerLeft_pb H e)
    (inferInstance : Flat e.left)
  have h3 := flat_mu H hH
  have k : (fst V V ≫ e) * (snd V V ≫ e) = ((e ▷ V) ≫ (H ◁ e)) ≫ μ[H] := by
    rw [Hom.mul_def]
    congr 1
    apply hom_ext <;> simp
  rw [k, Over.comp_left, Over.comp_left]
  infer_instance

end GlobalTheory.Mum.FlatMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalEndSecCoNonzeroLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem mem_basicOpen_of_comp {X Y Y' : Scheme.{0}} (c : Y ⟶ Y') (f : Y' ⟶ X) {U : X.Opens} (r : Γ(X, U))
    {y : Y} (h : y ∈ Y.basicOpen ((c ≫ f).app U r)) : c y ∈ Y'.basicOpen (f.app U r) := by
  rw [← Scheme.preimage_basicOpen] at h ⊢
  exact h

theorem secCoNonzero_of_comp {X Y Y' : Scheme.{0}} (L : LB X) {k k' : ℕ} (c : Y ⟶ Y') (u v : Y' ⟶ X)
    (s : H0 L k) (t : H0 L k') (h : SecCoNonzero L (c ≫ u) (c ≫ v) s t) : SecCoNonzero L u v s t := by
  obtain ⟨y, i, i', h1, h2⟩ := h
  exact ⟨c y, i, i', mem_basicOpen_of_comp c u _ h1, mem_basicOpen_of_comp c v _ h2⟩

theorem formalEnd_secCoNonzero_lift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), FormalEnd U.toUnifPre a h' b → ∀ (k k' : ℕ) (s : H0 U.LG.L k) (t : H0 U.LG.L k'), SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s t → ∀ e : ℕ, SecCoNonzero U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s t := by
  intro R _ _ _ _ D A G _ _ _ U a h' b hb k k' s t h0 e
  induction e with
  | zero => exact h0
  | succ e ih =>
    apply secCoNonzero_of_comp U.LG.L (thickMap R (maximalIdeal R) e G)
    have hf : thickMap R (maximalIdeal R) e G ≫ (fstG (maximalIdeal R) (e + 1) G).left =
        (fstG (maximalIdeal R) e G).left := (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    rw [hf, ← Category.assoc, hb.2.1 e, Category.assoc, hf]
    exact ih

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormsPrimitiveAbelianScheme
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.AbCoh.primF_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.PrimF A :=
  fun R _ A _ g hA hg ↦ GlobalTheory.AbCoh.PrimForm.prim_of_axes A (_root_.GlobalTheory.AbCoh.AxesForm.eq_zero_of_axes R A g hA hg)
end

