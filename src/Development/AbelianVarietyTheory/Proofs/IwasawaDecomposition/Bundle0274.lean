module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0109
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MkDetPtEqRelDetQ
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin unif ordF)
open GlobalTheory.Mem.Chr.RelDet GlobalTheory.Mem.Chr.IdlFact
open GlobalTheory.CharValCompare (IsFr)

namespace GlobalTheory.Mem.Col2.DetLat

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem ordSub_conj {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) N) (P : HeightOneSpectrum (𝓞 E)) :
    ordSub (conjPrime₂ P) (detSub N) = -ordSub P (detSub N) := by
  have hfr (w : HeightOneSpectrum (𝓞 E)) : IsFr w N (latFr w N) := by
    first | exact isFr_latFr w ⟨hN, hu⟩ | exact isFr_latFr w hN
  have hfull : Submodule.IsFullLattice E N := by
    letI : Submodule.IsLattice E N := hN
    refine ⟨?_⟩
    apply top_unique
    rw [← ((Pi.basisFun E (Fin n)).map (latFr P N)).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((hfr P _).2 (CharValCompare.single_mem_stdAt P i))
    have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
      intro h
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h)
      exact hs (this ▸ P.asIdeal.zero_mem)
    have hx' : (algebraMap (𝓞 E) E s) • (latFr P N) (Pi.single i 1) ∈ N := by
      rwa [IsScalarTower.algebraMap_smul]
    have hm := Submodule.smul_mem (Submodule.span E (N : Set (Sp E n)))
      (algebraMap (𝓞 E) E s)⁻¹ (Submodule.subset_span hx')
    rw [← mul_smul, inv_mul_cancel₀ hs0, one_smul] at hm
    simpa only [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe] using hm
  have h := CharValCompare.val_dual (P := P) ⟨hN, hu⟩ (hfr P) (hfr (conjPrime₂ P))
  rw [map_mul, valuation_star, CharValCompare.conjP_conjP] at h
  rw [ordSub_detSub_eq hfull (hfr P), ordSub_detSub_eq hfull (hfr (conjPrime₂ P))]
  unfold Formalism.L2.Host.ordF
  rw [eq_inv_of_mul_eq_one_right h, WithZero.log_inv]

theorem ordSub_std (w : HeightOneSpectrum (𝓞 E)) : ordSub w (detSub (stdLat E n)) = 0 := by
  have hfull : Submodule.IsFullLattice E (stdLat E n) := by
    letI : Submodule.IsLattice E (stdLat E n) := stdLat_lattice
    refine ⟨?_⟩
    apply top_unique
    rw [← ((Pi.basisFun E (Fin n)).map ((1 : Sp E n ≃ₗ[E] Sp E n))).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 (((show IsFr w (stdLat E n) 1 from fun _ => Iff.rfl) _).2 (CharValCompare.single_mem_stdAt w i))
    have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
      intro h
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h)
      exact hs (this ▸ w.asIdeal.zero_mem)
    have hx' : (algebraMap (𝓞 E) E s) • ((1 : Sp E n ≃ₗ[E] Sp E n)) (Pi.single i 1) ∈ (stdLat E n) := by
      rwa [IsScalarTower.algebraMap_smul]
    have hm := Submodule.smul_mem (Submodule.span E ((stdLat E n) : Set (Sp E n)))
      (algebraMap (𝓞 E) E s)⁻¹ (Submodule.subset_span hx')
    rw [← mul_smul, inv_mul_cancel₀ hs0, one_smul] at hm
    simpa only [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe] using hm
  rw [ordSub_detSub_eq (f := 1) hfull fun _ => Iff.rfl]
  simp [Formalism.L2.Host.ordF]


open Classical in
theorem ordI_detIdl (SB : Finset (HeightOneSpectrum (𝓞 E))) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    {fr : HeightOneSpectrum (𝓞 E) → Sp E n ≃ₗ[E] Sp E n} (hf : ∀ P, IsFr P N (fr P)) (w : HeightOneSpectrum (𝓞 E)) :
    ordI w (detIdl SB N fr) =
      if w ∈ SB then ordSub w (detSub N) else if conjPrime₂ w ∈ SB then 0 else ((ordSub w (detSub N)).toNat : ℤ) := by
  have hfull : Submodule.IsFullLattice E N := by
    letI : Submodule.IsLattice E N := hN
    refine ⟨?_⟩
    apply top_unique
    rw [← ((Pi.basisFun E (Fin n)).map (fr w)).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((hf w _).2 (CharValCompare.single_mem_stdAt w i))
    have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
      intro h
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h)
      exact hs (this ▸ w.asIdeal.zero_mem)
    have hx' : (algebraMap (𝓞 E) E s) • (fr w) (Pi.single i 1) ∈ N := by
      rwa [IsScalarTower.algebraMap_smul]
    have hm := Submodule.smul_mem (Submodule.span E (N : Set (Sp E n)))
      (algebraMap (𝓞 E) E s)⁻¹ (Submodule.subset_span hx')
    rw [← mul_smul, inv_mul_cancel₀ hs0, one_smul] at hm
    simpa only [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe] using hm
  have e : valAt w (detIdl SB N fr) = Valued.v (compAt w (detIdl SB N fr)) := valAt_apply _ _
  rw [ordI, e, compAt_detIdl SB hN]
  split_ifs
  · rw [valued_algebraMap, ordSub_detSub_eq hfull (hf w)]
    rfl
  · simp
  · have h := ordF_unif_self w
    unfold Formalism.L2.Host.ordF at h
    rw [map_pow, valued_algebraMap, WithZero.log_pow, neg_eq_iff_eq_neg.1 h]
    simp

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mk_mk_eq_of_ord {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) {a b : Neutral.B1.Ideles H.E}
    (h : ∀ w, ordI w a - ordI (conjPrime₂ w) a = ordI w b - ordI (conjPrime₂ w) b) :
    (QuotientGroup.mk (QuotientGroup.mk a) : DtQ H SQ ⧸ UOQ H SQ) = QuotientGroup.mk (QuotientGroup.mk b) := by
  refine QuotientGroup.eq.2 ?_
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mk_mem_UOQ, KDq_sup_unitIdl]
  refine (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H _).2 fun w w' hw => ?_
  rw [← valAt_apply, ← valAt_apply, valAt_eq, valAt_eq, ordI_mul, ordI_mul, ordI_inv, ordI_inv,
    (isConjPl_iff H w w').1 hw]
  have := h w
  congr 1
  omega

end GlobalTheory.Mem.Col2.DetLat

namespace GlobalTheory.Mem.Col2

open DetLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mk_detPt_eq_relDetQ : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (p : DecoF H.E n ST SG Q), LevOk H SG SQ → (QuotientGroup.mk (detPt H SQ p) : DtQ H SQ ⧸ UOQ H SQ) = relDetQ H SQ n (stdLat H.E n) p.deco.1.N := by
  intro R H n ST SG Q SQ p hL
  have hN := p.deco.2.lat
  have hf : {w | (ordSub w (detSub p.deco.1.N) - ordSub w (detSub (stdLat H.E n))).toNat ≠ 0}.Finite :=
    (finite_ordSub hN).subset fun v hv h0 => hv (by simp [h0, ordSub_std])
  refine mk_mk_eq_of_ord H SQ (a := ptIdl H SQ p)
    (b := powI fun w => (ordSub w (detSub p.deco.1.N) - ordSub w (detSub (stdLat H.E n))).toNat) fun w => ?_
  rw [ordI_powI _ hf, ordI_powI _ hf, ptIdl, ordI_detIdl _ hN (isFr_ptFr p), ordI_detIdl _ hN (isFr_ptFr p),
    CharValCompare.conjP_conjP, ordSub_std, ordSub_std, ordSub_conj hN p.deco.2.uni]
  have hs := hL.split w
  by_cases h1 : w ∈ uSG SG SQ
  · rw [if_pos h1, if_neg (hs h1), if_pos h1]
    omega
  · by_cases h2 : conjPrime₂ w ∈ uSG SG SQ
    · rw [if_neg h1, if_pos h2, if_pos h2]
      omega
    · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
      omega

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialOfNeBot
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.Pairs

section Abstract

variable {H S F P P' : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']

def img (j : P →ₗ[ℂ] S →ₗ[ℂ] F) : Submodule ℂ F := Submodule.span ℂ {φ | ∃ p v, j p v = φ}

theorem apply_mem_img (j : P →ₗ[ℂ] S →ₗ[ℂ] F) (p : P) (v : S) : j p v ∈ img j :=
  Submodule.subset_span ⟨p, v, rfl⟩

variable {ι : Type} [Fintype ι]

def total (b : ι → S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) : (ι → P) →ₗ[ℂ] F :=
  ∑ a, (LinearMap.applyₗ (b a)) ∘ₗ j ∘ₗ LinearMap.proj a

theorem total_apply (b : ι → S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) (c : ι → P) :
    total b j c = ∑ a, j (c a) (b a) := by
  simp [total, LinearMap.sum_apply]

theorem total_repr (b : Module.Basis ι ℂ S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) (p : P) (v : S) :
    total b j (fun a => b.repr v a • p) = j p v := by
  rw [total_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← b.sum_repr v, map_sum]
  simp

theorem range_total (b : Module.Basis ι ℂ S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) :
    LinearMap.range (total b j) = img j := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨c, rfl⟩
    rw [total_apply]
    exact Submodule.sum_mem _ fun a _ => apply_mem_img j _ _
  · rintro _ ⟨p, v, rfl⟩
    exact ⟨_, total_repr b j p v⟩

theorem coeff_mem {ρ : Representation ℂ H S} (hsp : Submodule.span ℂ (Set.range ρ) = ⊤) {R : H → Module.End ℂ F}
    {j : P →ₗ[ℂ] S →ₗ[ℂ] F} (hj : ∀ p x v, j p (ρ x v) = R x (j p v)) {U : Submodule ℂ F}
    (hU : ∀ x, ∀ u ∈ U, R x u ∈ U) (b : Module.Basis ι ℂ S) {c : ι → P} (h : total b j c ∈ U) (a : ι) (w : S) :
    j (c a) w ∈ U := by
  classical
  have key : ∀ T : Module.End ℂ S, ∑ a, j (c a) (T (b a)) ∈ U := fun T => by
    have hT : T ∈ Submodule.span ℂ (Set.range ρ) := hsp ▸ Submodule.mem_top
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      have e : ∑ a, j (c a) (ρ g (b a)) = R g (total b j c) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [total_apply, map_sum]
        exact Finset.sum_congr rfl fun a _ => hj _ _ _
      rw [e]
      exact hU _ _ h
    | zero => simp
    | add x y _ _ hx hy => simpa [Finset.sum_add_distrib] using add_mem hx hy
    | smul r x _ hx => simpa [Finset.smul_sum] using U.smul_mem r hx
  have h1 := key ((b.coord a).smulRight w)
  rw [Finset.sum_eq_single a (fun a' _ h' => by simp [Module.Basis.coord_apply, Finsupp.single_apply, h'])
    (fun h' => absurd (Finset.mem_univ a) h')] at h1
  simpa [Module.Basis.coord_apply] using h1

theorem eq_bot_or_eq_img [FiniteDimensional ℂ S] {K : Type} {ρ : Representation ℂ H S}
    (hsp : Submodule.span ℂ (Set.range ρ) = ⊤) {R : H → Module.End ℂ F} {j : P →ₗ[ℂ] S →ₗ[ℂ] F}
    (hj : ∀ p x v, j p (ρ x v) = R x (j p v)) {Q : K → Module.End ℂ P}
    {T : K → Module.End ℂ F} (hQ : ∀ k p v, j (Q k p) v = T k (j p v))
    (hP : ∀ N : Submodule ℂ P, (∀ k, ∀ p ∈ N, Q k p ∈ N) → N = ⊥ ∨ N = ⊤) {U : Submodule ℂ F} (hle : U ≤ img j)
    (hU : ∀ x, ∀ u ∈ U, R x u ∈ U) (hT : ∀ k, ∀ u ∈ U, T k u ∈ U) : U = ⊥ ∨ U = img j := by
  let N : Submodule ℂ P := ⨅ v : S, U.comap ((LinearMap.applyₗ v) ∘ₗ j)
  have hN : ∀ p, p ∈ N ↔ ∀ v, j p v ∈ U := fun p => by simp [N, Submodule.mem_iInf]
  rcases hP N fun k p hp => (hN _).2 fun v => by
      rw [hQ]
      exact hT _ _ ((hN p).1 hp v) with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun φ hφ => ?_
    let b := Module.finBasis ℂ S
    obtain ⟨c, rfl⟩ : φ ∈ LinearMap.range (total b j) := by
      rw [range_total]
      exact hle hφ
    have hc : ∀ a, c a = 0 := fun a => by
      have : c a ∈ N := (hN _).2 fun w => coeff_mem hsp hj hU b hφ a w
      rwa [h, Submodule.mem_bot] at this
    rw [total_apply]
    simp [hc]
  · right
    refine le_antisymm hle (Submodule.span_le.2 ?_)
    rintro _ ⟨p, v, rfl⟩
    exact (hN p).1 (h ▸ Submodule.mem_top) v

end Abstract

section Concrete

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_inf_mul_fin (x : UA E n) : ∃ a ∈ infU E n, ∃ k ∈ finU (E := E) (n := n), x = a * k := by
  let y : GL (Fin n) (Cinf E) := cInf x
  have hx : cT (conjAd E) x.1.val * 1 * x.1.val = 1 := x.2
  have h1 : x.1.val.map (pInf E) = y.val := rfl
  have h3 : (cT (conjAd E) x.1.val).map (pInf E) = y.valᴴ := by
    ext1 i j
    rw [Matrix.conjTranspose_apply, ← h1]
    exact (infEq E).symm_apply_apply _
  have hy : y.valᴴ * y.val = 1 := by
    rw [mul_one] at hx
    rw [← h3, ← h1, ← Matrix.map_mul, hx]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let a : UA E n := ⟨infGL E n y, infGL_mem_UA y hy⟩
  refine ⟨a, pFin_infGL y, a⁻¹ * x, ?_, (mul_inv_cancel_left a x).symm⟩
  have h4 : cInf a = y := pInf_infGL y
  refine MonoidHom.mem_ker.2 ?_
  rw [map_mul, map_inv, h4]
  exact inv_mul_cancel y

theorem stable_of {U : Submodule ℂ (UA E n → ℂ)} (h1 : ∀ x : infU E n, ∀ φ ∈ U, RU E n x.1 φ ∈ U)
    (h2 : ∀ k : finU (E := E) (n := n), ∀ φ ∈ U, RU E n k.1 φ ∈ U) (x : UA E n) (φ : UA E n → ℂ) (hφ : φ ∈ U) : RU E n x φ ∈ U := by
  obtain ⟨a, ha, k, hk, rfl⟩ := exists_inf_mul_fin x
  rw [← RU_RU]
  exact h1 ⟨a, ha⟩ _ (h2 ⟨k, hk⟩ _ hφ)

theorem exists_cAll (g : InfinitePlace E → GL (Fin n) ℂ)
    (hg : ∀ v, (g v : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ y : infU E n, cAll y.1 = g := by
  classical
  let J : Subgroup (InfinitePlace E → GL (Fin n) ℂ) := (cAll.comp (infU E n).subtype).range
  let Hs : InfinitePlace E → Subgroup (GL (Fin n) ℂ) := fun _ => (GlobalTheory.Branching.unitaryIncl n).range
  have hle : Subgroup.pi Set.univ Hs ≤ J := by
    rw [Subgroup.pi_le_iff]
    intro v
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    obtain ⟨e, he⟩ := _root_.GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n v.embedding
    let x := e.symm u
    have hx := Subgroup.mem_inf.1 x.2
    refine ⟨⟨x.1, hx.1⟩, ?_⟩
    funext v'
    by_cases h : v' = v
    · subst h
      change cEmb v'.embedding x.1 = _
      rw [← he, e.apply_symm_apply]
      simp
    · have h5 : x.1 ∈ (cEmb (E := E) (n := n) v'.embedding).ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 v'.embedding) (by simpa using h)
      change cEmb v'.embedding x.1 = _
      rw [MonoidHom.mem_ker.1 h5]
      simp [h]
  obtain ⟨y, hy⟩ : g ∈ J := hle fun v _ => ⟨⟨(g v).val, hg v⟩, Units.ext rfl⟩
  exact ⟨y, hy⟩

theorem span_rep (W : Wt E n) [Nontrivial W.Sp] : Submodule.span ℂ (Set.range W.rep) = ⊤ :=
  GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ W.rep ((CuspRep.isIrreducible_iff _).2 ⟨inferInstance, fun U hU =>
    GlobalTheory.CoefIrred.vv_irreducible_unitary (InfinitePlace E) n W U fun g hg x hx => by
      obtain ⟨y, rfl⟩ := exists_cAll g hg
      exact hU y x hx⟩)

def jOf (W : Wt E n) (M : Submodule ℂ (algForms W)) : M →ₗ[ℂ] W.Sp →ₗ[ℂ] (UA E n → ℂ) :=
  (algForms W).subtype ∘ₗ M.subtype

theorem jOf_injective (W : Wt E n) (M : Submodule ℂ (algForms W)) : Function.Injective (jOf W M) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem jOf_rep (W : Wt E n) (M : Submodule ℂ (algForms W)) (p : M) (x : infU E n) (v : W.Sp) :
    jOf W M p (W.rep x v) = RU E n x.1 (jOf W M p v) := p.1.2.2 x v

theorem nontrivial_of_ne_bot {W : Wt E n} {M : Submodule ℂ (algForms W)} (h : M ≠ ⊥) :
    Nontrivial W.Sp ∧ img (jOf W M) ≠ ⊥ := by
  obtain ⟨p, hp, h0⟩ := (Submodule.ne_bot_iff _).1 h
  have h1 : jOf W M ⟨p, hp⟩ ≠ 0 := fun e => h0 (congrArg Subtype.val (jOf_injective W M (e.trans (map_zero _).symm)))
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 h1
  refine ⟨⟨v, 0, fun e => hv (by rw [e, map_zero]; rfl)⟩, fun e => hv ?_⟩
  have := apply_mem_img (jOf W M) ⟨p, hp⟩ v
  rw [e, Submodule.mem_bot] at this
  exact this

theorem img_stable {W : Wt E n} {M : Submodule ℂ (algForms W)} (hM : ∀ k, ∀ f ∈ M, algRep W k f ∈ M) (x : UA E n)
    (φ : UA E n → ℂ) (hφ : φ ∈ img (jOf W M)) : RU E n x φ ∈ img (jOf W M) := by
  refine stable_of (fun a => ?_) (fun k => ?_) x φ hφ
  · have h1 : img (jOf W M) ≤ (img (jOf W M)).comap (RU E n a.1) := Submodule.span_le.2 (by
      rintro _ ⟨p, v, rfl⟩
      change RU E n a.1 _ ∈ img (jOf W M)
      rw [← jOf_rep]
      exact apply_mem_img _ _ _)
    exact fun φ hφ => h1 hφ
  · have h1 : img (jOf W M) ≤ (img (jOf W M)).comap (RU E n k.1) := Submodule.span_le.2 (by
      rintro _ ⟨p, v, rfl⟩
      exact apply_mem_img (jOf W M) ⟨algRep W k p.1, hM k _ p.2⟩ v)
    exact fun φ hφ => h1 hφ

theorem V_eq_img (π : AutSub E n) {W : Wt E n} {M : Submodule ℂ (algForms W)} (hM : ∀ k, ∀ f ∈ M, algRep W k f ∈ M)
    (h0 : M ≠ ⊥) (hle : M ≤ π.finPart W) : π.V = img (jOf W M) := by
  have h1 : img (jOf W M) ≤ π.V := Submodule.span_le.2 (by
    rintro _ ⟨p, v, rfl⟩
    exact AutSub.mem_finPart.1 (hle p.2) v)
  exact ((π.isAut.irred _ h1 (img_stable hM)).resolve_left (nontrivial_of_ne_bot h0).2).symm

theorem finPart_stable (π : AutSub E n) (W : Wt E n) : ∀ k, ∀ f ∈ π.finPart W, algRep W k f ∈ π.finPart W :=
  fun k _ h => AutSub.mem_finPart.2 fun v => π.isAut.stable k _ (AutSub.mem_finPart.1 h v)

section Iso

variable {π π' : AutSub E n} {W : Wt E n} (e : π.finPart W ≃ₗ[ℂ] π'.finPart W) (T : π.V ≃ₗ[ℂ] π'.V)
  (hA : π.V = img (jOf W (π.finPart W)))
  (hT : ∀ p v (h : jOf W (π.finPart W) p v ∈ π.V), (T ⟨jOf W (π.finPart W) p v, h⟩ : UA E n → ℂ) = jOf W (π'.finPart W) (e p) v)

include hA hT

end Iso

end Concrete

end GlobalTheory.DefU.Pairs

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalLevelFormMemFaceLevelMultiplicity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.DefiniteMult

theorem toMap_mem_levP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (Fn : Bridge.Gf D.sp.X' → R.cX.W), Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ → (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) → R.cX.toMap R.prX Fn ∈ Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB b t Fn hFn hP
  have h := GlobalTheory.DefiniteEnd.isMultMap_toMap hB.models.inf D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) R.MX hB.models.cX
    hB.models.prX hFn
  refine (mem_multT R.θ R.MX _ _ _).2 (Submodule.subset_span ⟨h.aut, h.cusp, fun v k hk g => ?_, h.equiv, h.cont⟩)
  have hkC : k ∈ GfC D.sp.X' := hk.1
  obtain ⟨hiff, hchi⟩ := _root_.GlobalTheory.TopBridge.mem_levelSubgroup_localDatum_iff D G Pl0 T A Ks R F hB.grp.red_R b t k hkC
  have hh := hiff.1 hk
  obtain ⟨hq, hp⟩ := hh
  have hc := hchi hq hp
  have hd := hP ⟨_, hq⟩ hp ((finHom D.sp.X').rangeRestrict g)
  have e : Fn ((finHom D.sp.X').rangeRestrict (g * k)) =
      levChi _ R.βX (datXP R t (R.levR F b)) k • Fn ((finHom D.sp.X').rangeRestrict g) :=
    (congrArg Fn (map_mul _ g k)).trans (hd.trans (congrArg (· • Fn ((finHom D.sp.X').rangeRestrict g)) hc.symm))
  have e2 : R.cX.ext Fn (g * k) = levChi _ R.βX (datXP R t (R.levR F b)) k • R.cX.ext Fn g :=
    ((congrArg (R.cX.ρ (g * k)⁻¹) e).trans
      (LinearMap.congr_fun (rho_right_inv R.cX.ρ g (hB.models.cX.1 _ (inv_mem hkC))) _)).trans (map_smul _ _ _)
  exact (congrArg (fun w => R.prX w (PiTensorProduct.tprod ℂ v)) e2).trans (LinearMap.congr_fun (map_smul R.prX _ _) _)

end GlobalTheory.DefiniteMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceScalarsErrorsReadings
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3


set_option maxHeartbeats 4000000 in
theorem reFace_scalars_errors_readings : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3), (∀ i, (Zsc (R.toCx3 F).zs).l6m i = (F.Zsc (R.toCx3 F).zs).l6m i ∨ ((∀ p, R.Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → R.PartAt F i p v)) → Pins R F cG → Holds R F → ∃ kap lam err, Pins ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) cG ∧ Holds ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ ErrEq ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ kap = R.kap ∧ (∀ i t p v, R.Wp3 i p ≠ ⊥ → lam i t p v = R.lam3 i t p v) ∧ ∃ (Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Z'.jW Z.jW := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Dc Sp Zsc hl6 hP hH
  refine ⟨R.kap, R.lam3, reFaceErr R F Dc Sp Zsc, ?_⟩
  exact ⟨reFace_pins R F cG Dc Sp Zsc _ hl6 hP,
    ⟨reFace_prim R F Dc Sp Zsc _ hH.prim, further_face_statements_independent_of_error R F Dc Sp Zsc _ hH.aux, hH.ok, hH.sep⟩,
    reFace_errEq R F Dc Sp Zsc, rfl, fun _ _ _ _ _ => rfl,
    reFaceRead R F Dc Sp Zsc _ X0 Y, reFaceReadL R F Dc Sp Zsc _ X0 Y Z,
    rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFockVectorEigenOfFiniteStepEigen
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.DTheta.StepLevFock

theorem om_ptY_of_finite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (t : T) (k : ℕ), k + 1 < D.R.m → ∀ κ ∈ GfC (Yc D k), ∀ κ' ∈ GfC (Yc D (k + 1)), ∀ c : ℂ, R.ωY t k (κ, κ') (R.vY t k) = c • R.vY t k → ∀ φ, R.ωY t k (κ, κ') (R.toRealDat.ptY t k φ) = c • R.toRealDat.ptY t k φ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH t k hk κ hκ κ' hκ' c hc φ
  have hch : R.toRealDat.IsChain := RealDat.chain_of_weak hP.char.base.chain hH.aux.ex
  exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ _ _ _ _ (R.ωY t k) hP.char.base.models.inf (hch.ωY t k hk)
    _ _ _ _ (R.vY t k) (hch.ptY t k hk) κ hκ κ' hκ' c hc φ

end GlobalTheory.Mem.R3.DTheta.StepLevFock
end

