module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Formalism.LocalToGlobal.Columns.Bundle0018
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.PairingDivisors.StatementH

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNegConjMemberHermitianLatticeSpaceData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.TripleSpace

theorem hasSig_neg_of_hasSignature {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (-M) q p := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨?_, ?_⟩
  · have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  · let Q : Matrix (Fin n) (Fin q ⊕ Fin p) ℂ := (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e Sum.swap
    refine ⟨Q.map star, ?_⟩
    have hQ : (Q.map star)ᵀ = Qᴴ := rfl
    have hQ2 : (Q.map star).map star = Q := by ext a b; simp
    rw [hQ, hQ2, Matrix.mul_neg, Matrix.neg_mul]
    have key : Qᴴ * M * Q = ((Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) *
        Matrix.reindex e e M * (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)).submatrix Sum.swap Sum.swap := by
      have hc : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) =
          (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ := by ext a b; rfl
      have hM : M = (Matrix.reindex e e M).submatrix e e := by ext a b; simp
      have hQh : Qᴴ = (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ.submatrix Sum.swap e := by
        simp only [Q, Matrix.conjTranspose_submatrix]
      rw [hc, hQh, hM, ← Matrix.submatrix_mul _ _ _ e _ e.bijective, Matrix.reindex_apply,
        Matrix.submatrix_submatrix]
      simp only [Q]
      rw [← Matrix.submatrix_mul _ _ _ e _ e.bijective]
      simp [Matrix.reindex_apply]
    rw [key, hP]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp [Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.one_apply]


open Formalism.IndefR.Datum in
theorem isCartan_neg_conj {n : ℕ} {G s : Matrix (Fin n) (Fin n) ℂ} (h : IsCartanInv G s) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (-(G.map star)) (-s) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hsG : sᴴ * G = G * s := by
    calc sᴴ * G = sᴴ * G * (s * s) := by rw [h1, Matrix.mul_one]
    _ = (sᴴ * G * s) * s := by simp only [Matrix.mul_assoc]
    _ = G * s := by rw [h2]
  have e2 : sᵀ * G.map star * s.map star = G.map star := by
    have := congrArg (fun X => X.map (starRingEnd ℂ)) h2
    simp only [Matrix.map_mul] at this
    have a1 : sᴴ.map (starRingEnd ℂ) = sᵀ := by ext a b; simp [Matrix.conjTranspose_apply]
    have a2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map (starRingEnd ℂ) = M.map star := fun M => rfl
    rw [a1, a2, a2] at this
    exact this
  refine ⟨by rw [neg_mul_neg, h1], ?_, ?_⟩
  · have e1 : (-s).map star = -(s.map star) := by ext a b; simp
    rw [e1, Matrix.transpose_neg]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, e2]
  · intro x hx
    have hz := h3.dotProduct_mulVec_pos hx
    have hGs : (G.map star) *ᵥ star x = star (G *ᵥ x) := by
      ext i; simp [Matrix.mulVec, dotProduct, star_sum]
    have key : ((-s) *ᵥ x) ⬝ᵥ ((-(G.map star)) *ᵥ star x) = star (star x ⬝ᵥ (G * s) *ᵥ x) := by
      rw [Matrix.neg_mulVec, Matrix.neg_mulVec, neg_dotProduct, dotProduct_neg, neg_neg, hGs,
        ← star_star (s *ᵥ x), star_dotProduct_star]
      congr 1
      rw [star_mulVec, dotProduct_comm, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hsG]
    rw [key, Complex.star_def, Complex.conj_re]
    exact (Complex.pos_iff.1 hz).1

theorem star_gram {D : D7} (V : HSp D) (a b : Fin V.rank) : star (V.gram a b) = V.gram b a :=
  V.herm.eq (V.frame a) (V.frame b)

theorem form_neg_eq {D : D7} (V : HSp D) (y x : Fin V.rank → D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((-1 : D.host.E) • V.gram) y x =
      -star (∑ i, ∑ j, star ((star x) i) * V.gram i j * (star y) j) := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, Matrix.smul_apply, star_sum, Pi.star_apply,
    star_star, star_mul', star_gram, Finset.mul_sum, smul_eq_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  show y b * (-1 * V.gram b a * star (x a)) = -(star (x a) * V.gram b a * y b)
  ring

theorem mem_starLat_iff_form {D : D7} (V : HSp D) {Λ₀ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hsd : IsSelfDualC V Λ₀) (y : Fin V.rank → D.host.E) :
    y ∈ Formalism.L2.Col.starLat D.host.E Λ₀ ↔ ∀ x ∈ Formalism.L2.Col.starLat D.host.E Λ₀,
      IsIntegral ℤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((-1 : D.host.E) • V.gram) y x) := by
  rw [Formalism.L2.Col.mem_starLat, hsd.2]
  constructor
  · intro H x hx
    obtain ⟨b, hb⟩ := H (star x) hx
    rw [form_neg_eq, ← hb]
    exact ((RingOfIntegers.isIntegral_coe b).map (starRingEnd D.host.E).toIntAlgHom).neg
  · intro H x hx
    have h := H (star x) (by rw [Formalism.L2.Col.mem_starLat, star_star]; exact hx)
    rw [form_neg_eq, star_star] at h
    have h2 := h.neg.map (starRingEnd D.host.E).toIntAlgHom
    rw [neg_neg] at h2
    exact ⟨⟨_, h2⟩, star_star (R := D.host.E) _⟩

theorem negConj_isHerm : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil)
    (i j : Fin D.R.m) (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau),
    (∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) →
    ∃ (Λ : Submodule (𝓞 D.host.E) (Fin (spW₁ G i j).rank → D.host.E))
      (bas : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin (spW₁ G i j).rank) (Fv D.host.F v)),
      Spc.IsHerm D.sp.cm.sig B
        (Spc.mk ((-1 : D.host.E) • (spW₁ G i j).gram) Λ (fun w => -W.cart (.grid (i : ℕ) (j : ℕ)) (τf w)) bas)
        ((D.R.m - j) / 2) ((spW₁ G i j).rank - (D.R.m - j) / 2) := by
  intro D T L sc G μ₀ hL W i j B τf hB
  have hR : Node.InRange D.R.m (.grid (i : ℕ) (j : ℕ)) := ⟨i.2.le, j.2.le⟩
  have hV := node_isV G hL hR
  have hsd : IsSelfDualC (spW₁ G i j) (G.Λ (.grid (i : ℕ) (j : ℕ))) := hV.sd
  have hlat : Submodule.IsFullLattice D.host.E (Formalism.L2.Col.starLat D.host.E (G.Λ (.grid (i : ℕ) (j : ℕ)))) := by
    let N := G.Λ (.grid (i : ℕ) (j : ℕ))
    have hN : Submodule.IsFullLattice D.host.E N :=
      Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hsd
    letI : Submodule.IsLattice D.host.E (Formalism.L2.Col.starLat D.host.E N) :=
      Formalism.L2.Col.brp_starLat_lattice D.host.E N hsd.1
    refine ⟨?_⟩
    have heq : star '' (N : Set (Fin (spW₁ G i j).rank → D.host.E)) =
        (Formalism.L2.Col.starLat D.host.E N : Set (Fin (spW₁ G i j).rank → D.host.E)) := by
      ext x
      change (∃ y, y ∈ N ∧ star y = x) ↔ star x ∈ N
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨star x, hx, star_star x⟩
    rw [← heq]
    exact Formalism.L2.Col.brp_star_span_top D.host.E _ (Submodule.IsFullLattice.span_eq_top (self := hN))
  have hb : ∀ v : B.P, ∃ β, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) (Formalism.L2.Col.starLat D.host.E (G.Λ (.grid (i : ℕ) (j : ℕ)))) β :=
    fun v => GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) _ (GlobalTheory.AdelicU.isCMExt_host D)
  refine ⟨Formalism.L2.Col.starLat D.host.E (G.Λ (.grid (i : ℕ) (j : ℕ))),
    fun v => if h : v ∈ B.P then (hb ⟨v, h⟩).choose else 1, ⟨?_, ?_, hlat, ?_, ?_, ?_⟩⟩
  · intro a b
    show star (((-1 : D.host.E) • (spW₁ G i j).gram) b a) = ((-1 : D.host.E) • (spW₁ G i j).gram) a b
    simp only [Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, star_one, star_gram]
  · intro w
    have hs := hV.sigOK (B.emb w).1
    rw [hV.sig, ← hV.rank] at hs
    have eJ : ((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1 = -((spW₁ G i j).gram.map (B.emb w).1) := by
      ext a b; simp
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1) _ _
    rw [eJ]
    exact hasSig_neg_of_hasSignature hs
  · intro y
    exact mem_starLat_iff_form (spW₁ G i j) hsd y
  · intro w
    have eJ : ((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1 =
        -((gramAt D (spW₁ G i j) (τf w)).map star) := by
      ext a b; simp [gramAt, hB]
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((-1 : D.host.E) • (spW₁ G i j).gram).map (B.emb w).1) _
    rw [eJ]
    exact isCartan_neg_conj (W.cart_is _ hR (τf w))
  · intro v
    show GlobalTheory.AdelicU.IsSplitBasis _ _ (if h : v.1 ∈ B.P then (hb ⟨v.1, h⟩).choose else 1)
    rw [dite_eq_left v.2]
    exact (hb v).choose_spec

end GlobalTheory.TripleSpace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulOfRankOne
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM Polynomial

theorem dvd_of_smul_end_eq_smul {R M : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] (f : Module.End R M) {a b : R} (ha : a ≠ 0)
    (h : ∀ x, a • f x = b • x) {x₀ : M} (hx₀ : x₀ ≠ 0) : a ∣ b := by
  obtain ⟨P, hP, hf⟩ := LinearMap.exists_monic_and_aeval_eq_zero R f
  have hpow : ∀ (i : ℕ) (x : M), a ^ i • (f ^ i) x = b ^ i • x := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      intro x
      rw [pow_succ f, Module.End.mul_apply, pow_succ' a, mul_smul, ih, smul_comm, h, pow_succ, mul_smul]
  have h0 : (P.scaleRoots a).eval b = 0 := by
    have h1 : (P.scaleRoots a).eval b • x₀ = a ^ P.natDegree • (aeval f P) x₀ := by
      rw [eval_eq_sum_range, aeval_eq_sum_range, natDegree_scaleRoots, Finset.sum_smul, LinearMap.sum_apply,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [coeff_scaleRoots, mul_smul, ← hpow, LinearMap.smul_apply, smul_smul, smul_smul, mul_assoc,
        pow_sub_mul_pow a hi', mul_comm]
    rw [hf, LinearMap.zero_apply, smul_zero, smul_eq_zero] at h1
    exact h1.resolve_right hx₀
  let K := FractionRing R
  have ha' : algebraMap R K a ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective R K)]
  have hc : algebraMap R K a * (algebraMap R K b / algebraMap R K a) = algebraMap R K b :=
    mul_div_cancel₀ _ ha'
  have hint : _root_.IsIntegral R (algebraMap R K b / algebraMap R K a) := by
    refine ⟨P, hP, ?_⟩
    have h2 := scaleRoots_eval₂_mul (p := P) (algebraMap R K) (algebraMap R K b / algebraMap R K a) a
    rw [hc, eval₂_at_apply, h0, map_zero] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left (pow_ne_zero _ ha')
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨g, IsFractionRing.injective R K ?_⟩
  rw [map_mul, hg, hc]

theorem exists_smul_of_rank_one (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (h : D.p + D.q = 1) (γ : D.La →+ D.La) (hγ : ∀ (s : 𝓞 E) (x : D.La), γ (s • x) = s • γ x) :
    ∃ g : 𝓞 E, ∀ x, γ x = g • x := by
  have := D.fin
  have := D.proj
  have hr : Module.finrank (𝓞 E) D.La = 1 := D.rank.trans h
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [hr]; exact one_pos)
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : D.La)
  obtain ⟨a, b, ha, hab⟩ := CMLat.exists_smul_eq_smul hr hx₀ (γ x₀)
  have key : ∀ x, a • γ x = b • x := fun x => by
    obtain ⟨r, s, hr0, e⟩ := CMLat.exists_smul_eq_smul hr hx₀ x
    have h1 : r • (a • γ x - b • x) = 0 := by
      rw [smul_sub, smul_comm r a, ← hγ, e, hγ, smul_comm a s, hab, smul_comm r b, e, smul_comm s b, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left hr0)
  let f : Module.End (𝓞 E) D.La := { toFun := γ, map_add' := γ.map_add, map_smul' := hγ }
  obtain ⟨g, rfl⟩ := dvd_of_smul_end_eq_smul f ha key hx₀
  refine ⟨g, fun x => ?_⟩
  have h1 : a • (γ x - g • x) = 0 := by rw [smul_sub, key, mul_smul, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left ha)

end GlobalTheory.FlatCM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.GoodPlace

theorem ncard_primesOver_eq_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {p : ℕ} (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 F)) (hpv : (p : 𝓞 F) ∈ v.asIdeal) :
    (v.asIdeal.primesOver (𝓞 E)).ncard = 2 := by
  classical
  haveI := v.isMaximal
  have hs := Ideal.sum_ramification_inertia (𝓞 E) F E (p := v.asIdeal) v.ne_bot
  rw [h2] at hs
  rw [← hs, ← IsDedekindDomain.coe_primesOverFinset v.ne_bot, Set.ncard_coe_finset, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot] at hq
  haveI := hq.1
  haveI := hq.2
  have hpq : (p : 𝓞 E) ∈ q := by
    simpa using (Ideal.mem_of_liesOver q v.asIdeal (p : 𝓞 F)).1 hpv
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ q := Ideal.map_le_iff_le_comap.2 (Ideal.LiesOver.over (P := q) (p := v.asIdeal)).le
  have he : v.asIdeal.ramificationIdx' q = 1 := by
    by_contra hne1
    have h3 := (Ideal.ramificationIdx'_ne_one_iff hle).1 hne1
    have h4 := h3 (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hpv)
    rw [map_natCast] at h4
    exact (GlobalTheory.LocSplit.split_prime hp h q hpq).1 h4
  have hcF := (GlobalTheory.ColClassCompare.unram_card_of_split (F := F) (E := E) hp h v.asIdeal hpv).2
  have hcE := (GlobalTheory.ColClassCompare.unram_card_of_split (F := E) (E := E) hp h q hpq).2
  have hf : v.asIdeal.inertiaDeg' q = 1 := by
    have hcomap : Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) q = v.asIdeal := (Ideal.LiesOver.over (P := q) (p := v.asIdeal)).symm
    rw [Ideal.inertiaDeg', dite_eq_left hcomap]
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
    have hfin : Module.Finite (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ q) := inferInstance
    have := Module.natCard_eq_pow_finrank (K := 𝓞 F ⧸ v.asIdeal) (V := 𝓞 E ⧸ q)
    rw [hcF, hcE] at this
    exact (Nat.pow_right_injective hp.two_le (by simpa using this.symm))
  rw [he, hf]

end GlobalTheory.GoodPlace

namespace GlobalTheory.GoodPlace

theorem exists_good_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (P₀ : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∃ v₁ : HeightOneSpectrum (𝓞 D.host.F), v₁ ∉ P₀ ∧
      SplitsFully D.host.E v₁ ∧ (∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v₁) ∧
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v₁) := by
  intro D T L sc G μ₀ _ t P₀
  classical
  set S : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
    P₀ ∪ (locPl G t).image (fun w => w.under (𝓞 D.host.F)) with hS
  have hn : D.host.QS ≠ 0 := D.host.QS_pos.ne'
  have hq : D.host.q ≠ 0 := D.host.hyp.1.ne_zero
  have hd : D.host.d ≠ 0 := D.host.hyp.2.1.ne_zero
  have hm : D.host.QS * D.host.q * D.host.d ≠ 0 := by positivity
  obtain ⟨p, hp, hlt, hc⟩ := Nat.exists_prime_gt_modEq_one (∑ u ∈ S, Ideal.absNorm u.asIdeal) hm
  obtain ⟨h1, -, -⟩ := GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc
  have h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E := by
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp]
    exact h1
  obtain ⟨v, hv⟩ := GlobalTheory.SplitChoice.exists_place_over D.host.F hp
  have hnot : ∀ u ∈ S, u ≠ v := by
    intro u hu e
    refine GlobalTheory.SplitChoice.natCast_notMem_of_absNorm_lt u hp ?_ (e ▸ hv)
    have := Finset.single_le_sum (f := fun u : HeightOneSpectrum (𝓞 D.host.F) => Ideal.absNorm u.asIdeal)
      (fun _ _ => Nat.zero_le _) hu
    omega
  refine ⟨v, fun hv0 => hnot v (Finset.mem_union_left _ hv0) rfl, ?_,
    fun w hw e => hnot _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw)) e, ?_⟩
  · have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
    have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      simpa using hv
    have hunder : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} :=
      (hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle).symm
    unfold SplitsFully
    rw [hunder]
    exact h
  · rw [GlobalTheory.AdelicU.nonempty_split_iff (GlobalTheory.AdelicU.isCMExt_host D)]
    exact ncard_primesOver_eq_two (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 hp h v hv

end GlobalTheory.GoodPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueMuPInfinityHodgeTateLatticeMap
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.ConstMu

theorem frobenius_ofPadic {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (c : ℤ_[p]) :
    WittVector.frobenius (ofPadic p O c) = ofPadic p O c := by
  ext n
  rw [WittVector.coeff_frobenius_charP]
  simp only [ofPadic, RingHom.comp_apply, WittVector.map_coeff]
  rw [← map_pow, ZMod.pow_card]

theorem frobenius_phiInv' {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (a : Ainf p O) :
    WittVector.frobenius (phiInv p O a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, phiInv, WittVector.map_coeff]
  exact frobeniusEquiv_symm_pow_p _ p _

theorem frobenius_mu' {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) = WittVector.frobenius (xi ε) * Sandwich.mu ε := by
  conv_lhs => rw [← xi_mul_nu, map_mul, ← phiInv_mu, frobenius_phiInv']

theorem existsUnique_lattMap : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ g : latt (PDivGroup.mu p O) →ₗ[Ainf p O] latt (const p O), (∀ m m' : latt (PDivGroup.mu p O), (∀ t, m'.1 t = WittVector.frobenius (m.1 t)) → ∀ t, (g m').1 t = WittVector.frobenius ((g m).1 t)) → ∃! f : const p O ⟶ PDivGroup.mu p O, lattMap f = g := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε g hg
  obtain ⟨ec, hec⟩ := _root_.GlobalTheory.PDivLat.latt_const_equiv p C v O hv ε hε
  obtain ⟨em, hem⟩ := _root_.GlobalTheory.MuLattice.latt_mu_equiv p C v O hv ε hε
  have eig := _root_.GlobalTheory.PDivLat.existsUnique_padic_of_eigen p C v O hv ε hε
  set l : latt (PDivGroup.mu p O) := em.symm 1 with hl_def
  have hl : l.1 (epsTate hε) = Sandwich.mu ε := by
    rw [← hem l, hl_def, LinearEquiv.apply_symm_apply, mul_one]
  have htate : ∀ t : (PDivGroup.mu p O).Tate, ∃ a : ℤ_[p], t = a • epsTate hε := by
    intro t
    obtain ⟨a, rfl⟩ := (epsEquiv hε).surjective t
    exact ⟨a, rfl⟩
  have hlval : ∀ a : ℤ_[p], l.1 (a • epsTate hε) = ofPadic p O a * Sandwich.mu ε := by
    intro a
    rw [map_smulₛₗ, hl, smul_eq_mul]
  have hgen : ∀ y : latt (PDivGroup.mu p O), y = em y • l := by
    intro y
    apply em.injective
    rw [map_smul, hl_def, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have hpull : ∀ (f : const p O ⟶ PDivGroup.mu p O) (y : latt (PDivGroup.mu p O)),
      ec (lattMap f y) = y.1 (tateMap _ _ O f (constGen p O)) := by
    intro f y
    rw [hec]
    rfl

  set b : Ainf p O := ((g l).1 (constGen p O)) with hb_def
  have hbeig : WittVector.frobenius b = WittVector.frobenius (xi ε) * b := by
    have h1 := hg l (WittVector.frobenius (xi ε) • l) (by
      intro t
      obtain ⟨a, rfl⟩ := htate t
      rw [Submodule.coe_smul, LinearMap.smul_apply, hlval, smul_eq_mul, map_mul,
        frobenius_ofPadic, frobenius_mu']
      ring) (constGen p O)
    rw [map_smul, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [hb_def, ← h1]
  obtain ⟨c, hc, hcu⟩ := eig b hbeig
  have hfix : ∀ f : const p O ⟶ PDivGroup.mu p O, lattMap f = g ↔
      ec (lattMap f l) = ec (g l) := by
    intro f
    constructor
    · intro h; rw [h]
    · intro h
      apply LinearMap.ext
      intro y
      rw [hgen y, map_smul, map_smul, ec.injective h]
  refine ⟨constHom (PDivGroup.mu p O) (c • epsTate hε), ?_, ?_⟩
  · show lattMap _ = g
    rw [hfix, hpull, tateMap_constHom, hlval, hec, hc]
  · intro f hf
    rw [hfix, hpull, hec] at hf
    obtain ⟨a, ha⟩ := htate (tateMap _ _ O f (constGen p O))
    rw [ha, hlval] at hf
    have hac : a = c := hcu a hf
    rw [← (constHom (PDivGroup.mu p O)).apply_symm_apply f, constHom_symm_apply, ha, hac]

end GlobalTheory.PDivLat.ConstMu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCompactInterUnitaryRationalPoints
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem compact_inter_ratPts_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (K : Set (GAd σ J)),
    IsCompact K → (K ∩ ratPts σ J).Finite := by
  intro F E _ _ _ _ _ σ n J K hK
  have hd : DiscreteTopology (ratPts σ J) := inferInstance
  have hcl : IsClosed ((ratPts σ J : Subgroup (GAd σ J)) : Set (GAd σ J)) := Subgroup.isClosed_of_discrete
  exact (hK.inter_right hcl).finite
    (IsDiscrete.mono (isDiscrete_iff_discreteTopology.2 hd) Set.inter_subset_right)

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanInfLogNormEmbeddingEqLogNormDivStatement
section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanInf_log_norm_embedding_eq_log_norm_div : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (a : K), a ≠ 0 → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding a‖) = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / Module.finrank ℚ K := by
  first | exact @GlobalTheory.meanInf_log_norm_embedding | exact GlobalTheory.meanInf_log_norm_embedding | (intros; apply GlobalTheory.meanInf_log_norm_embedding <;> assumption)
end

