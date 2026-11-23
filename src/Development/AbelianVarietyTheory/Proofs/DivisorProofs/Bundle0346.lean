module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalKaehlerDBasisSmoothSubalgebra
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD


set_option maxHeartbeats 1000000 in
open TensorProduct in
theorem exists_notMem_smul_D_mem_span (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K)
    [IsFractionRing B K] [Algebra.Smooth k B] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    (P : Ideal B) [P.IsPrime] :
    ∃ (f : B) (u : Fin d → B), f ∉ P ∧
      ∀ v : B, f • D k B v ∈ Submodule.span B (Set.range fun j => D k B (u j)) := by
  haveI : Algebra.FormallyEtale B K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  have hinj : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  haveI : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).2 hinj
  have hrk : Module.finrank B Ω[B⁄k] = d := by
    rw [← hd, (KaehlerDifferential.isBaseChange_of_formallyEtale k B K).finrank_eq]
  have hfib : Module.finrank P.ResidueField (P.ResidueField ⊗[B] Ω[B⁄k]) = d := by
    rw [← hrk]; exact Ideal.finrank_fiber_eq_finrank P

  let g : B → P.ResidueField ⊗[B] Ω[B⁄k] := fun v => (1 : P.ResidueField) ⊗ₜ D k B v
  have hg : Submodule.span P.ResidueField (Set.range g) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul a m =>
      have h1 : (1 : P.ResidueField) ⊗ₜ[B] m ∈ Submodule.span P.ResidueField (Set.range g) := by
        have hm : m ∈ Submodule.span B (Set.range (D k B)) := by
          rw [KaehlerDifferential.span_range_derivation]; trivial
        induction hm using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨v, rfl⟩ := hy
          exact Submodule.subset_span ⟨v, rfl⟩
        | zero => rw [tmul_zero]; exact zero_mem _
        | add y z _ _ hy hz => rw [tmul_add]; exact add_mem hy hz
        | smul r y _ hy =>
          rw [tmul_smul, ← algebraMap_smul P.ResidueField r]
          exact Submodule.smul_mem _ _ hy
      have : a ⊗ₜ[B] m = a • ((1 : P.ResidueField) ⊗ₜ[B] m) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [this]; exact Submodule.smul_mem _ _ h1
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent P.ResidueField (Set.range g)
  let bs : Module.Basis s P.ResidueField (P.ResidueField ⊗[B] Ω[B⁄k]) :=
    Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hg])
  haveI : Finite s := Module.Finite.finite_basis bs
  letI : Fintype s := Fintype.ofFinite s
  have hcard : Fintype.card s = d := by rw [← Module.finrank_eq_card_basis bs, hfib]
  let bF := bs.reindex (Fintype.equivFinOfCardEq hcard)
  have hu : ∀ j, ∃ v, g v = bF j := by
    intro j
    have : bF j ∈ s := by
      rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]; exact Subtype.prop _
    exact hs this
  choose u hu using hu

  let N : Submodule B Ω[B⁄k] := Submodule.span B (Set.range fun j => D k B (u j))
  let φ := (N.mkQ).baseChange P.ResidueField
  have hφ : φ = 0 := by
    refine bF.ext fun j => ?_
    rw [← hu j]
    simp only [φ, g, LinearMap.baseChange_tmul, LinearMap.zero_apply]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 (Submodule.subset_span ⟨j, rfl⟩)]
    exact TensorProduct.tmul_zero _ _
  have hsub : Subsingleton (P.ResidueField ⊗[B] (Ω[B⁄k] ⧸ N)) := by
    have h0 : ∀ x : P.ResidueField ⊗[B] (Ω[B⁄k] ⧸ N), x = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | add x y hx hy => rw [hx, hy, add_zero]
      | tmul a q =>
        obtain ⟨m, rfl⟩ := N.mkQ_surjective q
        have := LinearMap.congr_fun hφ (a ⊗ₜ m)
        simpa only [φ, LinearMap.baseChange_tmul, LinearMap.zero_apply] using this
    exact ⟨fun x y => by rw [h0 x, h0 y]⟩
  have hnot : (⟨P, inferInstance⟩ : PrimeSpectrum B) ∉ Module.support B (Ω[B⁄k] ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]
    exact hsub
  rw [Module.mem_support_iff_of_finite] at hnot
  obtain ⟨f, hf, hfP⟩ := Set.not_subset.1 hnot
  have hfN : ∀ v : B, f • D k B v ∈ N := fun v => by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact Module.mem_annihilator.1 hf _
  exact ⟨f, u, hfP, hfN⟩

end GlobalTheory.PD

namespace GlobalTheory.PD

theorem exists_local_dbasis (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K)
    [IsFractionRing B K] [Algebra.Smooth k B] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    (P : Ideal B) [P.IsPrime] :
    ∃ (f : B) (u : Fin d → B) (b : Module.Basis (Fin d) K Ω[K⁄k]), f ∉ P ∧ (∀ j, b j = D k K (u j : K)) ∧
      ∀ (v : B) (j : Fin d), ∃ c : B, (f : K) * b.repr (D k K (v : K)) j = c := by
  obtain ⟨f, u, hfP, hfN⟩ := exists_notMem_smul_D_mem_span k K B d hd P
  have hinj : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  have hf0 : (f : K) ≠ 0 := by
    intro h
    apply hfP
    have : f = 0 := hinj (by rw [map_zero]; exact h)
    rw [this]; exact P.zero_mem
  have hcoef : ∀ v : B, ∃ c : Fin d → B,
      (f : K) • D k K (v : K) = ∑ j, (c j : K) • D k K (u j : K) := by
    intro v
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 (hfN v)
    refine ⟨c, ?_⟩
    have := congrArg (KaehlerDifferential.map k k B K) hc
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smul, KaehlerDifferential.map_D, Subalgebra.smul_def] at this
    exact this.symm
  let W : Submodule K Ω[K⁄k] := Submodule.span K (Set.range fun j => D k K (u j : K))
  have hB : ∀ v : B, D k K (v : K) ∈ W := by
    intro v
    obtain ⟨c, hc⟩ := hcoef v
    have h1 : (f : K) • D k K (v : K) ∈ W := by
      rw [hc]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have := Submodule.smul_mem W (f : K)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hf0, one_smul] at this
  have hK : ∀ w : K, D k K w ∈ W := by
    intro w
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B) w
    have hy0 : algebraMap B K y ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hy)
    have hx : D k K (algebraMap B K x) = (algebraMap B K x / algebraMap B K y) • D k K (algebraMap B K y)
        + algebraMap B K y • D k K (algebraMap B K x / algebraMap B K y) := by
      conv_lhs => rw [show algebraMap B K x = algebraMap B K x / algebraMap B K y * algebraMap B K y by
        rw [div_mul_cancel₀ _ hy0]]
      rw [Derivation.leibniz, add_comm]
    have h2 : algebraMap B K y • D k K (algebraMap B K x / algebraMap B K y) ∈ W := by
      have e : algebraMap B K y • D k K (algebraMap B K x / algebraMap B K y) =
          D k K (algebraMap B K x) - (algebraMap B K x / algebraMap B K y) • D k K (algebraMap B K y) := by
        rw [hx]; abel
      rw [e]
      exact sub_mem (hB x) (Submodule.smul_mem _ _ (hB y))
    have := Submodule.smul_mem W (algebraMap B K y)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hy0, one_smul] at this
  have htop : ⊤ ≤ W := by
    rw [← KaehlerDifferential.span_range_derivation k K]
    exact Submodule.span_le.2 (Set.range_subset_iff.2 hK)
  let b := basisOfTopLeSpanOfCardEqFinrank (fun j => D k K (u j : K)) htop (by rw [Fintype.card_fin, hd])
  have hb : ∀ j, b j = D k K (u j : K) := fun j => by
    simp only [b, coe_basisOfTopLeSpanOfCardEqFinrank]
  refine ⟨f, u, b, hfP, hb, fun v j => ?_⟩
  obtain ⟨c, hc⟩ := hcoef v
  refine ⟨c j, ?_⟩
  have h3 : b.repr ((f : K) • D k K (v : K)) j = (c j : K) := by
    rw [hc]
    simp_rw [← hb]
    rw [b.repr_sum_self (fun j => (c j : K))]
  rw [← h3, map_smul, Finsupp.smul_apply, smul_eq_mul]

end GlobalTheory.PD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheaf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.DiscChains

def heExt {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] {K L : ChainComplex C ℕ}
    (h : HomotopyEquiv K L) :
    HomotopyEquiv (K.extend ComplexShape.embeddingDownNat) (L.extend ComplexShape.embeddingDownNat) where
  hom := HomologicalComplex.extendMap h.hom _
  inv := HomologicalComplex.extendMap h.inv _
  homotopyHomInvId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((h.homotopyHomInvId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((h.homotopyInvHomId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))

variable (R : Type) [CommRing R]

def heN (P : PSh) :
    HomotopyEquiv ((chainsN R).obj (disc.obj P)) ((ChainComplex.single₀ (Shv R)).obj ((free R).obj P)) :=
  (HomotopyEquiv.ofIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).mapIso
      (Functor.constComp _ P (free R)))).trans
    (SimplicialObject.Augmented.ExtraDegeneracy.const ((free R).obj P)).homotopyEquiv

lemma heN_inv_f_zero (P : PSh) :
    (heN R P).inv.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 _).hom := by
  dsimp [heN, HomotopyEquiv.trans, HomotopyEquiv.ofIso, SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv]
  erw [HomologicalComplex.comp_f]
  erw [ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  simp
  exact Category.comp_id _

def he (P : PSh) : HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)) :=
  (HomotopyEquiv.ofIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat ((free R).obj P) 0 0
      (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl)).symm).trans
    (heExt (heN R P)).symm

lemma he_hom_f_zero (P : PSh) : sglι _ ≫ (he R P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv := by
  dsimp [he, heExt, HomotopyEquiv.trans, HomotopyEquiv.symm, HomotopyEquiv.ofIso]
  erw [HomologicalComplex.comp_f, HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl), heN_inv_f_zero]
  rw [sglι, chainsXIso]
  erw [Category.assoc, Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  erw [Iso.inv_hom_id_assoc]
  erw [Iso.inv_hom_id_assoc]

end GlobalTheory.EtC.DiscChains

namespace GlobalTheory.EtC

theorem chains_disc_homotopyEquiv : ∀ (R : Type) [CommRing R] , ∃ e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)), (∀ P, sglι _ ≫ (e P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv) ∧ ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) = (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom := by
  intro R _
  refine ⟨DiscChains.he R, DiscChains.he_hom_f_zero R, fun {P Q} f => ?_⟩
  obtain ⟨-, hnat, -⟩ := GlobalTheory.EtC.chains_basic R
  apply HomologicalComplex.from_single_hom_ext
  apply (Iso.cancel_iso_inv_left (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((free R).obj P)) _ _).1
  change sglι _ ≫ _ = sglι _ ≫ _
  have e1 : ((DiscChains.he R P).hom ≫ (chains R).map (disc.map f)).f 0 =
      (DiscChains.he R P).hom.f 0 ≫ ((chains R).map (disc.map f)).f 0 := HomologicalComplex.comp_f _ _ _
  have e2 : ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (DiscChains.he R Q).hom).f 0 =
      ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f)).f 0 ≫ (DiscChains.he R Q).hom.f 0 :=
    HomologicalComplex.comp_f _ _ _
  rw [e1, e2, ← Category.assoc, DiscChains.he_hom_f_zero]
  have h1 : sglι ((free R).obj P) ≫ ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f)).f 0 =
      (free R).map f ≫ sglι ((free R).obj Q) := by
    change _ ≫ ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f)).f 0 = _
    rw [HomologicalComplex.single_map_f_self]
    erw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, h1, Category.assoc, DiscChains.he_hom_f_zero]
  rw [← cancel_mono (chainsXIso R (disc.obj Q) 0).hom]
  have h2 := hnat (disc.map f) 0
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [h2]
  simp

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroIsNilpotentMulFiniteInfFgIdeals
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.FinInterNil

theorem exists_ne_zero_isNilpotent_mul {D E : Type} [CommRing D] [IsDomain D] [CommRing E]
    [Algebra D E] (y : E)
    (hy : ∀ Q : Ideal E, Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → y ∈ Q) :
    ∃ t : D, t ≠ 0 ∧ IsNilpotent (algebraMap D E t * y) := by
  by_contra hcon
  push_neg at hcon
  let M : Submonoid E :=
    { carrier := {z | ∃ t : D, t ≠ 0 ∧ ∃ n : ℕ, z = algebraMap D E t * y ^ n}
      mul_mem' := by
        rintro a b ⟨t, ht, n, rfl⟩ ⟨t', ht', m, rfl⟩
        exact ⟨t * t', mul_ne_zero ht ht', n + m, by rw [map_mul, pow_add]; ring⟩
      one_mem' := ⟨1, one_ne_zero, 0, by simp⟩ }
  have h0 : (0 : E) ∉ M := by
    rintro ⟨t, ht, n, hz⟩
    apply hcon t ht
    refine ⟨n + 1, ?_⟩
    calc (algebraMap D E t * y) ^ (n + 1)
        = algebraMap D E t ^ n * y * (algebraMap D E t * y ^ n) := by ring
      _ = 0 := by rw [← hz, mul_zero]
  have hdisj : Disjoint ((⊥ : Ideal E) : Set E) (M : Set E) := by
    rw [Set.disjoint_left]
    intro z hz hzM
    have hz0 : z = 0 := by simpa using hz
    exact h0 (hz0 ▸ hzM)
  obtain ⟨Q, hQ, -, hQM⟩ := Ideal.exists_le_prime_disjoint ⊥ M hdisj
  have hcomap : Q.comap (algebraMap D E) = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [Ideal.mem_bot]
    by_contra htne
    have hm : algebraMap D E t ∈ M := ⟨t, htne, 0, by simp⟩
    exact Set.disjoint_left.mp hQM (Ideal.mem_comap.mp ht) hm
  have hyQ := hy Q hQ hcomap
  have hm : y ∈ M := ⟨1, one_ne_zero, 1, by simp⟩
  exact Set.disjoint_left.mp hQM hyQ hm

theorem main : ∀ (D E : Type) [CommRing D] [IsDomain D] [CommRing E] [Algebra D E] (ι : Type)
    (X : Finset ι) (P : ι → Ideal E), (∀ i ∈ X, (P i).FG) →
    (∀ Q : Ideal E, Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → (⨅ i ∈ X, P i) ≤ Q) →
    ∃ s : D, s ≠ 0 ∧ ∀ y ∈ (⨅ i ∈ X, P i), IsNilpotent (algebraMap D E s * y) := by
  intro D E _ _ _ _ ι X P hFG hQ
  classical
  have hstep : ∀ y ∈ (⨅ i ∈ X, P i), ∃ t : D, t ≠ 0 ∧ IsNilpotent (algebraMap D E t * y) :=
    fun y hy => exists_ne_zero_isNilpotent_mul y (fun Q hQp hQc => hQ Q hQp hQc hy)
  have hJfg : (∏ i ∈ X, P i).FG := by
    refine Finset.prod_induction P (fun J : Ideal E => J.FG) (fun a b ha hb => ha.mul hb) ?_ hFG
    exact ⟨{1}, by simp⟩
  have hJI : ∀ g ∈ ∏ i ∈ X, P i, g ∈ (⨅ i ∈ X, P i) := by
    intro g hg
    simp only [Submodule.mem_iInf]
    intro i hi
    exact (Ideal.prod_le_inf.trans (Finset.inf_le hi)) hg
  obtain ⟨S, hS⟩ := hJfg
  have hSI : ∀ g : S, (g : E) ∈ (⨅ i ∈ X, P i) := fun g =>
    hJI g (hS ▸ Submodule.subset_span g.2)
  choose t ht using fun g : S => hstep g.1 (hSI g)
  refine ⟨∏ g : S, t g, Finset.prod_ne_zero_iff.mpr (fun g _ => (ht g).1), ?_⟩
  set s := ∏ g : S, t g with hs
  let K : Ideal E := Submodule.comap (LinearMap.mulLeft E (algebraMap D E s)) (nilradical E)
  have hK : ∀ z, z ∈ K ↔ IsNilpotent (algebraMap D E s * z) := by
    intro z
    simp [K, mem_nilradical]
  have hJK : (∏ i ∈ X, P i) ≤ K := by
    rw [← hS, Submodule.span_le]
    intro g hg
    rw [SetLike.mem_coe, hK]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ (⟨g, hg⟩ : S))
    have he : algebraMap D E s * g = algebraMap D E c * (algebraMap D E (t ⟨g, hg⟩) * g) := by
      rw [hs, hc, map_mul]; ring
    rw [he]
    exact (Commute.all _ _).isNilpotent_mul_left (ht ⟨g, hg⟩).2
  intro y hy
  have hyN : y ^ X.card ∈ ∏ i ∈ X, P i := by
    have := Ideal.prod_mem_prod (s := X) (I := P) (x := fun _ => y) (fun i hi => by
      have := hy
      simp only [Submodule.mem_iInf] at this
      exact this i hi)
    simpa [Finset.prod_const] using this
  have hn := (hK _).mp (hJK hyN)
  have hpow : IsNilpotent ((algebraMap D E s * y) ^ (X.card + 1)) := by
    have he : (algebraMap D E s * y) ^ (X.card + 1)
        = (algebraMap D E s ^ X.card * y) * (algebraMap D E s * y ^ X.card) := by ring
    rw [he]
    exact (Commute.all _ _).isNilpotent_mul_left hn
  obtain ⟨k, hk⟩ := hpow
  exact ⟨(X.card + 1) * k, by rw [pow_mul, hk]⟩

end GlobalTheory.FinInterNil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteTypeSubringInValuationSubring
section
open Polynomial

namespace GlobalTheory

theorem finiteDimensional_top_subfield (L : Type*) [Field L] :
    FiniteDimensional (⊤ : Subfield L) L := by
  refine ⟨⟨{1}, eq_top_iff.mpr fun l _ => ?_⟩⟩
  rw [Finset.coe_singleton, Submodule.mem_span_singleton]
  exact ⟨⟨l, Subfield.mem_top l⟩, mul_one l⟩

theorem exists_normal_finiteType_subring_of_valuationSubring : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ R : Subring K, ∃ hcR : ∀ a, c a ∈ R, (c.codRestrict R hcR).FiniteType ∧ R ≤ (V.comap φ).toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R K ∧ (∀ x ∈ t, ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) := by
  intro K L _ _ φ c hfin V hc t ht hgen
  classical
  letI : Algebra ℂ K := c.toAlgebra
  letI : Algebra K L := φ.toAlgebra
  letI : Algebra ℂ L := (φ.comp c).toAlgebra
  haveI : IsScalarTower ℂ K L := .of_algebraMap_eq fun _ => rfl
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℂ L).injective
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
  have ht' : ∀ x : t, ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0 :=
    fun x => (ht x x.2).2
  choose p hpm hpc hpx using ht'
  let T : Set K := ⋃ x : t, ((p x).coeffs : Set K)
  have hT : T.Finite := Set.finite_iUnion fun x => (p x).coeffs.finite_toSet
  let A : Subalgebra ℂ K := Algebra.adjoin ℂ T
  haveI : Algebra.FiniteType ℂ A := .adjoin_of_finite hT
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hcoefA : ∀ x : t, ∀ n, (p x).coeff n ∈ A := fun x n => by
    by_cases h : (p x).coeff n = 0
    · rw [h]; exact A.zero_mem
    · exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨x, Polynomial.coeff_mem_coeffs h⟩)
  have hAE : ∀ y ∈ A, y ∈ V.comap φ := fun y hy => by
    let E' : Subalgebra ℂ K := { (V.comap φ).toSubring with algebraMap_mem' := fun a => hc a }
    have : A ≤ E' := Algebra.adjoin_le (by
      intro y hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
      obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
      exact hpc x i)
    exact this hy
  haveI : IsScalarTower A K L := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℂ A L := .of_algebraMap_eq fun _ => rfl
  have hint : ∀ x : t, IsIntegral A (x : L) := fun x => by
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap A K)
      ((lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, hcoefA x n⟩, rfl⟩) (hpm x)
    refine ⟨q, hqm, ?_⟩
    rw [← hpx x, ← hq, eval₂_map]
    rfl

  have hsub : Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)) ≤ (integralClosure A L).toSubring :=
    Subring.closure_le.mpr (Set.union_subset
      (by
        rintro _ ⟨a, rfl⟩
        exact isIntegral_algebraMap (R := A) (x := (⟨c a, A.algebraMap_mem a⟩ : A)))
      (fun x hx => hint ⟨x, hx⟩))
  have hall : ∀ l : L, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)),
      ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)), (l = b / d ∨ l⁻¹ = b / d) := by
    intro l
    rcases V.mem_or_inv_mem l with h | h
    · obtain ⟨b, hb, d, hd, -, -, he⟩ := hgen l h
      exact ⟨b, hb, d, hd, Or.inl he⟩
    · obtain ⟨b, hb, d, hd, -, -, he⟩ := hgen _ h
      exact ⟨b, hb, d, hd, Or.inr he⟩
  haveI : Algebra.IsAlgebraic A L := ⟨fun l => by
    obtain ⟨b, hb, d, hd, h⟩ := hall l
    have hb' : IsAlgebraic A b := (hsub hb : IsIntegral A b).isAlgebraic
    have hd' : IsAlgebraic A d := (hsub hd : IsIntegral A d).isAlgebraic
    have hbd : IsAlgebraic A (b / d) := by rw [div_eq_mul_inv]; exact hb'.mul hd'.inv
    rcases h with h | h
    · rw [h]; exact hbd
    · rw [← inv_inv l, h]; exact hbd.inv⟩
  haveI : Algebra.IsAlgebraic A K := ⟨fun k =>
    (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom A K L) φ.injective).mp
      (Algebra.IsAlgebraic.isAlgebraic (φ k))⟩
  have htop : Subfield.closure (Set.range (algebraMap ℂ L) ∪ (t : Set L)) = ⊤ := by
    refine eq_top_iff.mpr fun l _ => ?_
    have hle : Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)) ≤
        (Subfield.closure (Set.range (algebraMap ℂ L) ∪ (t : Set L))).toSubring :=
      Subring.closure_le.mpr Subfield.subset_closure
    obtain ⟨b, hb, d, hd, h⟩ := hall l
    have hbd := Subfield.div_mem _ (hle hb) (hle hd)
    rcases h with h | h
    · rw [h]; exact hbd
    · rw [← inv_inv l, h]; exact Subfield.inv_mem _ hbd
  haveI : Algebra.EssFiniteType ℂ L := by
    refine essFiniteType_of_finiteDimensional_subfield_closure t.finite_toSet ?_
    rw [htop]
    exact finiteDimensional_top_subfield L
  haveI : Algebra.EssFiniteType A L := .of_comp ℂ A L
  haveI : Module.Finite A (integralClosure A L) :=
    GlobalTheory.finite_integralClosure_of_essFiniteType_field ℂ A L
  let S := integralClosure A K
  let f : S →ₐ[A] integralClosure A L :=
    ((IsScalarTower.toAlgHom A K L).comp S.val).codRestrict _ fun z =>
      (z.2.map (IsScalarTower.toAlgHom A K L) : IsIntegral A _)
  haveI : Module.Finite A S := Module.Finite.of_injective f.toLinearMap fun z w h =>
    Subtype.ext (φ.injective (congrArg Subtype.val h : _))
  set_option synthInstance.maxHeartbeats 200000 in
    haveI : Algebra.FiniteType ℂ S := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
    haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
    haveI : IsFractionRing S K := integralClosure.isFractionRing_of_algebraic fun x hx => Subtype.ext hx
    haveI : IsIntegrallyClosed S := (isIntegrallyClosed_iff K).mpr fun {x} hx =>
      ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩

    have hcR : ∀ a, c a ∈ S.toSubring := fun a => S.algebraMap_mem (⟨c a, A.algebraMap_mem a⟩ : A)
    refine ⟨S.toSubring, hcR, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℂ S)
    · intro x hx
      obtain ⟨q, hqm, hq⟩ := (hx : IsIntegral A x)
      let ι : A →+* V.comap φ :=
        { toFun := fun a => ⟨a, hAE a a.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hE : IsIntegral (V.comap φ) x := by
        refine ⟨q.map ι, hqm.map ι, ?_⟩
        rw [eval₂_map]
        exact hq
      obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hE
      exact y.2
    · exact (inferInstance : IsNoetherianRing S)
    · exact (inferInstance : IsIntegrallyClosed S)
    · exact (inferInstance : IsFractionRing S K)
    · intro x hx
      obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic (f := S.toSubring.subtype)
        ((lifts_iff_coeff_lifts _).mpr fun n =>
          ⟨⟨_, S.algebraMap_mem (⟨_, hcoefA ⟨x, hx⟩ n⟩ : A)⟩, rfl⟩) (hpm ⟨x, hx⟩)
      refine ⟨q, hqm, ?_⟩
      rw [← eval₂_map, hq]
      exact hpx ⟨x, hx⟩

end GlobalTheory
end

