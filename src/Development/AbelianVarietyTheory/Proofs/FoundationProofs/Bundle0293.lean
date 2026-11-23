module

public import Mathlib
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0140

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitAt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedSplit

open GlobalTheory.SplitIdem GlobalTheory.IdemModTwo

theorem idem_alg {T : Type} [CommRing T] (p U R w w' : T) (hU : p * U = U)
    (hR : R * R - (w + w') * R + w * w' * p = 0) (hδ : (w + w') * U - 2 * (U * R) = p) :
    (U * w - U * R) * (U * w - U * R) = U * w - U * R ∧
      (U * w - U * R) * (U * w' - U * R) = 0 ∧
      (U * w - U * R) + (U * w' - U * R) = p := by
  have h2 : (U * w - U * R) * (U * w' - U * R) = 0 := by
    linear_combination U * U * hR - w * w' * U * hU
  refine ⟨?_, h2, by linear_combination hδ⟩
  linear_combination (U * w - U * R) * hδ - h2 + (w - R) * hU

theorem idem_tensor {F A E K : Type} [Field F] [CommRing A] [Algebra F A] [CommRing E] [Algebra F E]
    [CommRing K] [Algebra F K] (φ : K →ₙ+* A)
    (hφ : ∀ (t : F) (y : K), φ (algebraMap F K t * y) = algebraMap F A t * φ y)
    (c : A ⊗[F] E →+* A ⊗[F] E) (a b : E) (t n : F) (r u : K)
    (hc1 : ∀ x : A, c (x ⊗ₜ 1) = x ⊗ₜ 1) (hca : ∀ x : A, c (x ⊗ₜ a) = x ⊗ₜ b)
    (ht : algebraMap F E t = a + b) (hn : algebraMap F E n = a * b)
    (hr : r * r - algebraMap F K t * r + algebraMap F K n = 0) (hu : u * (algebraMap F K t - 2 * r) = 1)
    (e : A ⊗[F] E) (he : e = φ u ⊗ₜ a + φ (-(u * r)) ⊗ₜ 1) :
    e * e = e ∧ e * c e = 0 ∧ e + c e = algebraMap A (A ⊗[F] E) (φ 1) := by
  let j : A →+* A ⊗[F] E := algebraMap A _
  let k : E →+* A ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E)
  have hjk : ∀ a x, a ⊗ₜ[F] x = j a * k x := fun a x => by
    simp [j, k, Algebra.TensorProduct.tmul_mul_tmul]
  have hF : ∀ s : F, j (algebraMap F A s) = k (algebraMap F E s) := fun s => by
    have h := hjk 1 (algebraMap F E s)
    rw [tmul_algebraMap_eq, mul_one, map_one, one_mul] at h
    exact h
  have h1 : e = j (φ u) * k a - j (φ u) * j (φ r) := by
    rw [he, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one]; ring
  have h2 : c e = j (φ u) * k b - j (φ u) * j (φ r) := by
    rw [he, map_add (f := _), hc1, hca, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one]; ring
  rw [h2, h1]
  refine idem_alg (j (φ 1)) _ _ _ _ ?_ ?_ ?_
  · rw [← map_mul, ← map_mul, one_mul]
  · have : φ r * φ r - algebraMap F A t * φ r + algebraMap F A n * φ 1 = 0 := by
      rw [← hφ, ← hφ, ← map_mul, ← map_sub, ← map_add (f := _), mul_one, hr, map_zero]
    have h := congrArg j this
    rwa [map_add, map_sub, map_mul, map_mul, map_mul, hF, hF, ht, hn, map_add, map_mul, map_zero] at h
  · have : algebraMap F A t * φ u - 2 * (φ u * φ r) = φ 1 := by
      rw [two_mul, ← hφ, ← map_mul, ← map_add (f := _), ← map_sub, ← hu]; congr 1; ring
    have h := congrArg j this
    rwa [map_sub, map_mul, map_mul, map_mul, map_ofNat, hF, ht, map_add] at h

theorem exists_root (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t n : 𝓞 F)
    (ht : t ∉ v.asIdeal) (hn : n ∈ v.asIdeal) :
    ∃ r u : v.adicCompletionIntegers F,
      r * r - algebraMap (𝓞 F) (v.adicCompletionIntegers F) t * r +
        algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = 0 ∧
      u * (algebraMap (𝓞 F) (v.adicCompletionIntegers F) t - 2 * r) = 1 := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have hm : algebraMap (𝓞 F) (v.adicCompletionIntegers F) n ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff]
    exact fun h => h hn
  have hT : IsUnit (algebraMap (𝓞 F) (v.adicCompletionIntegers F) t) :=
    (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v t).2 ht
  generalize algebraMap (𝓞 F) (v.adicCompletionIntegers F) t = T at hT
  generalize algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = N at hm
  obtain ⟨r, hr, hr0⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
    (Polynomial.X ^ 2 - Polynomial.C T * Polynomial.X + Polynomial.C N) (by monicity!) 0
    (by simpa using hm) (by simpa using hT.map _)
  rw [sub_zero] at hr0
  have hunit : IsUnit (T - 2 * r) := by
    by_contra h
    have h1 : T - 2 * r ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := h
    have h2 := Ideal.add_mem _ h1 (Ideal.mul_mem_left _ 2 hr0)
    rw [sub_add_cancel] at h2
    exact h2 hT
  obtain ⟨u, hu⟩ := hunit.exists_left_inv
  refine ⟨r, u, ?_, hu⟩
  simpa [Polynomial.IsRoot, pow_two] using hr

theorem exists_int (D : D7) (x : 𝓞 D.host.E) (hx : star (x : D.host.E) = x) :
    ∃ t : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = x ∧
      algebraMap D.host.F D.host.E (t : D.host.F) = x := by
  obtain ⟨t, ht⟩ := exists_of_star_eq D hx
  have hxint : IsIntegral ℤ (x : D.host.E) := x.2
  have hi : IsIntegral ℤ t :=
    (isIntegral_algebraMap_iff).1 (ht ▸ hxint)
  exact ⟨⟨t, hi⟩, RingOfIntegers.ext ht, ht⟩

theorem exists_splitAt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), GlobalTheory.UnRep.SplitPl (GlobalTheory.Member.cF D) v → ∃ e : Formalism.L2.Theta.AE D, GlobalTheory.IdemModTwo.SplitAt D v e := by
  rintro D v ⟨P, hP, hPv, a, ha, b, hb, hbP⟩
  have hb' : (b : D.host.E) = star (a : D.host.E) := hb
  obtain ⟨t, ht, ht'⟩ := exists_int D (a + b) (by
    show star ((a : D.host.E) + b) = (a : D.host.E) + b
    rw [hb', star_add, star_star, add_comm])
  obtain ⟨n, hn, hn'⟩ := exists_int D (a * b) (by
    show star ((a : D.host.E) * b) = (a : D.host.E) * b
    rw [hb', star_mul', star_star, mul_comm])
  have htv : t ∉ v.asIdeal := by
    rw [← hPv, Ideal.mem_comap, ht]
    exact fun h => hbP ((Ideal.add_mem_iff_right P ha).1 h)
  have hnv : n ∈ v.asIdeal := by
    rw [← hPv, Ideal.mem_comap, hn]
    exact Ideal.mul_mem_right _ _ ha
  obtain ⟨r, u, hr, hu⟩ := exists_root D.host.F v t n htv hnv
  have key := idem_tensor (placeHom D.host.F v) (fun s y => by
      refine Prod.ext (mul_zero _).symm ?_
      show singleV D.host.F v _ = algebraMap D.host.F (Af D.host.F) s * singleV D.host.F v y
      rw [singleV_mul, AlgHom.commutes])
    (cA D) (a : D.host.E) (b : D.host.E) (t : D.host.F) (n : D.host.F) (r : Fv D.host.F v) (u : Fv D.host.F v)
    (fun x => by rw [cA_tmul, star_one]) (fun x => by rw [cA_tmul, hb']) ht' hn'
    (congrArg Subtype.val hr) (congrArg Subtype.val hu) _ rfl
  exact ⟨_, key⟩

end GlobalTheory.MovedSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeFinTrivial

theorem mem_closure_range {F E ι : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (τ : ι → E →+* ℂ) (θ : ι → (InfiniteAdeleRing F ⊗[F] E →+* ℂ))
    (h1 : ∀ i (x : E), θ i ((1 : InfiniteAdeleRing F) ⊗ₜ[F] x) = τ i x)
    (h2 : ∀ i, Continuous fun a : InfiniteAdeleRing F => θ i (a ⊗ₜ[F] (1 : E)))
    (y : InfiniteAdeleRing F ⊗[F] E) :
    (fun i => θ i y) ∈ closure (Set.range fun (k : E) i => τ i k) := by
  let S : AddSubgroup (ι → ℂ) := (RingHom.pi τ).toAddMonoidHom.range.topologicalClosure
  show (fun i => θ i y) ∈ S
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact S.zero_mem
  | add a b ha hb => simp only [map_add (f := _)]; exact S.add_mem ha hb
  | tmul a x =>
    have e : ∀ (a : InfiniteAdeleRing F) i, θ i (a ⊗ₜ[F] x) = θ i (a ⊗ₜ[F] (1 : E)) * τ i x := by
      intro a i
      rw [← h1, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hc : Continuous fun (a : InfiniteAdeleRing F) i => θ i (a ⊗ₜ[F] x) := by
      refine continuous_pi fun i => ?_
      simp only [e]
      exact (h2 i).mul continuous_const
    refine DenseRange.induction_on (InfiniteAdeleRing.denseRange_algebraMap F) a
      (isClosed_closure.preimage hc) fun f => ?_
    refine subset_closure ⟨f • x, funext fun i => ?_⟩
    show τ i (f • x) = θ i (algebraMap F _ f ⊗ₜ[F] x)
    rw [← h1, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem denseRange_units {E ι : Type} [Field E] [Finite ι] [Nonempty ι] (τ : ι → E →+* ℂ)
    (h : DenseRange fun (k : E) i => τ i k) :
    DenseRange fun (k : Eˣ) i => Units.map (τ i).toMonoidHom k := by
  have hg : Topology.IsOpenEmbedding (Pi.map (fun _ : ι => (Units.val : ℂˣ → ℂ))) :=
    Topology.IsOpenEmbedding.piMap (fun w => Units.isOpenEmbedding_val)
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := h.exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty ι := inferInstance
    have h1 := congrFun hk w
    beta_reduce at h1
    rw [map_zero] at h1
    exact (v w).ne_zero h1
  refine ⟨v, hv, Units.mk0 k hk0, ?_⟩
  funext w
  exact Units.ext (congrFun hk w).symm


set_option maxHeartbeats 1000000 in
open GlobalTheory.FockCompare in
theorem eq_one_of_trivial_on_finite : ∀ (D : D7) (c : (AE D)ˣ →* Circle), IsHeckeChar D c → (∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → c x = 1) → ∀ x, c x = 1 := by
  intro D c hc hf
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  let θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun τ => θ' (tauE D τ)
  have hθ : IsInfFam θ := fun τ => hθ' _
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ ρ hρ r1 r0
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  haveI : Nonempty D.what₂.Tau :=
    ⟨((GlobalTheory.CMTypePlaces.places_bijective D).2 (Classical.arbitrary _)).choose⟩
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  have tc : Continuous t :=
    (hs.cont.comp (continuous_pi fun τ => Units.continuous_val.comp (continuous_apply τ))).add continuous_const
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have Tc : Continuous T.toHomUnits := Units.continuous_iff.2 ⟨tc, tc.comp continuous_inv⟩
  have hT : ∀ x : (AE D)ˣ, c x = c (T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) := by
    intro x
    have h1 : a x = T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x :=
      Units.ext (ext _ _ ((ha x).2.trans (tf _).symm) fun τ =>
        (congrArg (θ τ) (ha x).1).trans (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) τ).symm)
    rw [← h1]
    conv_lhs => rw [hab x, map_mul, hf _ (hb x).1, mul_one]
  have hd : DenseRange fun (k : D.host.E) τ => tauE D τ k := by
    intro z
    have := mem_closure_range (tauE D) θ (fun τ => (hθ τ).1) (fun τ => (hθ τ).2) (infPart D (s z))
    rwa [show (fun i => θ i (infPart D (s z))) = z from funext fun τ => hs.comp z τ] at this
  intro x
  rw [hT]
  generalize (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) = z
  refine (denseRange_units (tauE D) hd).induction_on z
    (isClosed_eq (hc.1.comp Tc) continuous_const) fun k => ?_
  refine Eq.trans ?_ ((hT _).symm.trans (hc.2 k))
  congr 2
  funext τ
  exact Units.ext ((hθ τ).1 k).symm

end GlobalTheory.HeckeFinTrivial
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharLocProd

noncomputable def evalAt {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    FiniteAdeleRing (𝓞 E) E →+* P.adicCompletion E where
  toFun x := x P
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem val_algebraMap {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (P.adicCompletion E) a) = P.valuation E a :=
  P.valuedAdicCompletion_eq_valuation' a

theorem evalAt_algebraMap {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    evalAt P (algebraMap E (FiniteAdeleRing (𝓞 E) E) a) = algebraMap E (P.adicCompletion E) a := rfl

theorem eq_prod_of_components {E : Type} [Field E] [NumberField E] {R A B : Type} [CommRing R] [CommRing A]
    [CommRing B] (p : R →+* A) (q : R →+* B) (inc : E →+* R)
    (ev : ∀ P : HeightOneSpectrum (𝓞 E), B →+* P.adicCompletion E)
    (hinc : ∀ P a, ev P (q (inc a)) = algebraMap E _ a)
    (I : AddSubgroup B) (hint : ∀ y, y ∈ I ↔ ∀ P, Valued.v (ev P y) ≤ 1)
    (e : HeightOneSpectrum (𝓞 E) → R) (hinf : ∀ P, p (e P) = 0) (h1 : ∀ P, ev P (q (e P)) = 1)
    (h0 : ∀ P P', P' ≠ P → ev P' (q (e P)) = 0) (c : Rˣ →* Circle) (N : ℕ) (hN : 0 < N)
    (hker : ∀ x : Rˣ, (p x = 1 ∧ q x ∈ I ∧ q (x⁻¹ : Rˣ) ∈ I) → (∃ y ∈ I, q x - 1 = N • y) → c x = 1)
    (x : Rˣ) (hx : p x = 1) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : HeightOneSpectrum (𝓞 E) → Eˣ)
    (l : HeightOneSpectrum (𝓞 E) → Rˣ) (hl : ∀ P, (l P : R) = 1 + e P * (inc (k P) - 1))
    (hS : ∀ P ∈ S, Valued.v (ev P (q x)) = P.valuation E (k P : E) ∧
      Valued.v (ev P (q x) - algebraMap E _ (k P : E)) ≤ P.valuation E (N : E) * P.valuation E (k P : E))
    (hS' : ∀ P, P ∉ S → Valued.v (ev P (q x)) = 1 ∧ (N : 𝓞 E) ∉ P.asIdeal) :
    c x = ∏ P ∈ S, c (l P) := by
  classical
  obtain ⟨u, hud⟩ : ∃ u : Rˣ, u = ∏ P ∈ S, l P := ⟨_, rfl⟩
  have hu : (u : R) = ∏ P ∈ S, (l P : R) := by
    simp only [hud, Units.coe_prod]
  have huinf : p u = 1 := by
    rw [hu, map_prod]
    refine Finset.prod_eq_one fun P _ => ?_
    simp [hl, hinf]
  have hloc1 : ∀ P, ev P (q (l P)) = algebraMap E _ (k P : E) := by
    intro P
    simp only [hl, map_add (f := _), map_mul, map_sub, map_one, h1, hinc]
    ring
  have hloc0 : ∀ P Q, Q ≠ P → ev Q (q (l P)) = 1 := by
    intro P Q hQ
    simp only [hl, map_add (f := _), map_mul, map_sub, map_one, h0 P Q hQ]
    ring
  have huS : ∀ P ∈ S, ev P (q u) = algebraMap E _ (k P : E) := by
    intro P hP
    rw [hu, map_prod, map_prod, Finset.prod_eq_single P, hloc1]
    · intro Q _ hQ; exact hloc0 Q P hQ.symm
    · intro h; exact absurd hP h
  have huS' : ∀ P, P ∉ S → ev P (q u) = 1 := by
    intro P hP
    rw [hu, map_prod, map_prod]
    refine Finset.prod_eq_one fun Q hQ => hloc0 Q P ?_
    rintro rfl; exact hP hQ
  obtain ⟨y, hy⟩ : ∃ y : Rˣ, y = x * u⁻¹ := ⟨_, rfl⟩
  have hxu : x = y * u := by rw [hy, inv_mul_cancel_right]
  have hyu : (y : R) * u = x := by
    rw [← Units.val_mul, hxu]
  have hyinf : p y = 1 := by
    have := congrArg p hyu
    rwa [map_mul, huinf, hx, mul_one] at this
  have hyev : ∀ P, ev P (q y) * ev P (q u) = ev P (q x) := by
    intro P
    rw [← map_mul, ← map_mul, hyu]
  have hk0 : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E (k P : E) ≠ 0 :=
    fun P => (Valuation.ne_zero_iff _).2 (k P).ne_zero
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hyv : ∀ P, Valued.v (ev P (q y)) = 1 := by
    intro P
    have := congrArg Valued.v (hyev P)
    rw [map_mul] at this
    by_cases hP : P ∈ S
    · rw [huS P hP, val_algebraMap, (hS P hP).1] at this
      exact mul_right_cancel₀ (hk0 P) (by rw [this, one_mul])
    · rwa [huS' P hP, map_one, mul_one, (hS' P hP).1] at this
  have hyv' : ∀ P, Valued.v (ev P (q (y⁻¹ : Rˣ))) = 1 := by
    intro P
    have : Valued.v (ev P (q y)) * Valued.v (ev P (q (y⁻¹ : Rˣ))) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, map_one]
    rwa [hyv, one_mul] at this
  have hcong : ∀ P, Valued.v (ev P (q y) - 1) ≤ P.valuation E (N : E) := by
    intro P
    by_cases hP : P ∈ S
    · have h2 := (hS P hP).2
      rw [← hyev P, huS P hP, ← sub_one_mul, map_mul, val_algebraMap] at h2
      exact le_of_mul_le_mul_right h2 (zero_lt_iff.2 (hk0 P))
    · have h2 : P.valuation E (N : E) = 1 := by
        have := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P
          (r := (N : 𝓞 E))).2 (hS' P hP).2
        simpa using this
      rw [h2]
      exact Valuation.map_sub_le _ (hyv P).le (by rw [map_one])
  have hcy : c y = 1 := by
    refine hker y ⟨hyinf, (hint _).2 fun P => (hyv P).le, (hint _).2 fun P => (hyv' P).le⟩
      ⟨q (inc (N : E)⁻¹) * (q y - 1), (hint _).2 fun P => ?_, ?_⟩
    · rw [map_mul, map_mul, hinc, val_algebraMap, map_sub, map_one, map_inv₀]
      have hv : 0 < P.valuation E (N : E) :=
        zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hN0)
      exact (inv_mul_le_one₀ hv).2 (hcong P)
    · rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (q.comp inc) N,
        RingHom.comp_apply, ← map_mul, ← map_mul, mul_inv_cancel₀ hN0, map_one, map_one, one_mul]
  rw [hxu, map_mul, hcy, one_mul, hud, map_prod]

theorem char_eq_prod_locK : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → ∀ (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → ∃ N : ℕ, 0 < N ∧ ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k : HeightOneSpectrum (𝓞 D.host.E) → D.host.Eˣ), (∀ P ∈ S, Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) ∧ Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤ P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k P : D.host.E)) → (∀ P, P ∉ S → Valued.v (ι (finPart D (x : AE D)) P) = 1 ∧ (N : 𝓞 D.host.E) ∉ P.asIdeal) → ((c x : Circle) : ℂ) = ∏ P ∈ S, ((χ.locK P (k P) : ℂˣ) : ℂ) := by
  intro D ι hι hint hidem c χ hc
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc.1.1
  refine ⟨N, hN, fun x hx S k hS hS' => ?_⟩
  choose e he hinf h1 h0 using hidem
  have key := eq_prod_of_components (infPart D) (finPart D) (incA D)
    (fun P => (evalAt P).comp ι.toRingHom)
    (fun P a => (congrArg (evalAt P) (hι a)).trans (evalAt_algebraMap P a))
    (intAE D) hint e hinf h1 h0 c N hN hker x hx S k (fun P => locU (he P).1 (k P)) (fun _ => rfl) hS hS'
  rw [key]
  exact (map_prod Circle.coeHom _ _).trans
    (Finset.prod_congr rfl fun P _ => hc.2 P (e P) (he P) (k P) _ rfl)

end GlobalTheory.CharLocProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
section
namespace GlobalTheory.AdelicU

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))

omit [NumberField E] in
theorem mem_levelOpen_iff_projFin {g : GAd σ J} :
    g ∈ levelOpen σ J L ↔ projFin σ J g ∈ levelOffFin σ J L ∅ := by
  simp [mem_levelOpen, mem_levelOffFin]

omit [NumberField E] in
theorem mem_stabLoc_iff_embLocFin {v : HeightOneSpectrum (𝓞 F)} {g : GLoc σ J v} :
    g ∈ stabLoc σ J L v ↔ embLocFin σ J v g ∈ levelOffFin σ J L ∅ := by
  rw [mem_levelOffFin]
  refine ⟨fun h => ⟨by simp, fun u _ => ?_⟩, fun h => by simpa using h.2 v (by simp)⟩
  by_cases e : u = v
  · subst e; simpa using h
  · rw [projFinLoc_embLocFin_ne σ J e]; exact one_mem _

omit [NumberField E] in
theorem image_ofFin_levelOffFin (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ofFin σ J '' (levelOffFin σ J L S : Set (GFin σ J)) = (levelOff σ J L S : Set (GAd σ J)) := by
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hg
    have h : g ∈ (ofFin σ J).range := by rw [range_ofFin]; exact (mem_levelOff.1 hg).1
    obtain ⟨y, rfl⟩ := h
    exact ⟨y, hg, rfl⟩

variable [Submodule.IsFullLattice E L]

theorem isOpen_isCompact_levelOffFin_empty :
    IsOpen (levelOffFin σ J L ∅ : Set (GFin σ J)) ∧ IsCompact (levelOffFin σ J L ∅ : Set (GFin σ J)) := by
  have hfg : L.FG := Submodule.IsLattice.fg (A := E) L
  obtain ⟨K, hK, ho, hc⟩ := GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab F E σ n J L hfg
    Submodule.IsFullLattice.span_eq_top
  have e : levelOffFin σ J L ∅ = K := by
    ext g
    have h := mem_levelOpen_iff_latHat σ J hfg (ofFin σ J g)
    have h2 : Formalism.MainNotions.StandardLattice.finMat σ J (ofFin σ J g) = (HA.mat (Af F) σ J g).1 :=
      congrArg (fun x => (HA.mat (Af F) σ J x).1) (projFin_ofFin σ J g)
    rw [mem_levelOpen_iff_projFin, projFin_ofFin, h2] at h
    exact h.trans (hK g).symm
  rw [e]
  exact ⟨ho, hc⟩

theorem isOpen_levelOffFin_empty : IsOpen (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
  (isOpen_isCompact_levelOffFin_empty σ J L).1

theorem isOpen_levelOpen : IsOpen (levelOpen σ J L : Set (GAd σ J)) := by
  have : (levelOpen σ J L : Set (GAd σ J)) = projFin σ J ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
    Set.ext fun _ => mem_levelOpen_iff_projFin σ J L
  rw [this]
  exact (isOpen_levelOffFin_empty σ J L).preimage (continuous_projFin σ J)

theorem isOpen_stabLoc (v : HeightOneSpectrum (𝓞 F)) : IsOpen (stabLoc σ J L v : Set (GLoc σ J v)) := by
  have : (stabLoc σ J L v : Set (GLoc σ J v)) = embLocFin σ J v ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
    Set.ext fun _ => mem_stabLoc_iff_embLocFin σ J L
  rw [this]
  exact (isOpen_levelOffFin_empty σ J L).preimage (continuous_embLocFin σ J v)

theorem isCompact_stabLoc (v : HeightOneSpectrum (𝓞 F)) : IsCompact (stabLoc σ J L v : Set (GLoc σ J v)) := by
  have : (stabLoc σ J L v : Set (GLoc σ J v)) = embLocFin σ J v ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
    Set.ext fun _ => mem_stabLoc_iff_embLocFin σ J L
  rw [this]
  exact (Function.LeftInverse.isClosedEmbedding (projFinLoc_embLocFin_self σ J v) (continuous_projFinLoc σ J v)
    (continuous_embLocFin σ J v)).isCompact_preimage (isOpen_isCompact_levelOffFin_empty σ J L).2

theorem isCompact_levelOffFin (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsCompact (levelOffFin σ J L S : Set (GFin σ J)) := by
  have : (levelOffFin σ J L S : Set (GFin σ J)) =
      (levelOffFin σ J L ∅ : Set (GFin σ J)) ∩ ofFin σ J ⁻¹' (awayPts σ J S : Set (GAd σ J)) := by
    ext g
    change ofFin σ J g ∈ levelOff σ J L S ↔ ofFin σ J g ∈ levelOff σ J L ∅ ∧ ofFin σ J g ∈ awayPts σ J S
    simp only [levelOff_eq, finAwayPts, Subgroup.mem_inf, awayPts_empty, Subgroup.mem_top]
    tauto
  rw [this]
  exact (isOpen_isCompact_levelOffFin_empty σ J L).2.inter_right
    ((isClosed_awayPts σ J S).preimage (continuous_ofFin σ J))

theorem isCompact_levelOff (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsCompact (levelOff σ J L S : Set (GAd σ J)) := by
  rw [← image_ofFin_levelOffFin]
  exact (isCompact_levelOffFin σ J L S).image (continuous_ofFin σ J)

theorem isCompact_levelFin : IsCompact (levelFin σ J L : Set (GAd σ J)) := isCompact_levelOff σ J L ∅

end GlobalTheory.AdelicU
end

