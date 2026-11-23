module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaOfOfIsCharLab
section
noncomputable section

namespace GlobalTheory.Mem.TypePl

open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.MemN GlobalTheory.GLq GlobalTheory.GLp NumberField IsDedekindDomain
open scoped Pointwise

section Places

variable {R : Ranks} {H : Host R}

theorem isConjPl_iff_conjPl (w w' : PlE H) : IsConjPl H w w' ↔ Chr.ConjPl H.conj.toRingEquiv w w' :=
  (HalfPlaces.isConjPl_iff H w w').trans (Chr.conjPl_iff_smul H.conj w w').symm

theorem under_eq_iff (w w' : PlE H) : w'.under (𝓞 H.F) = w.under (𝓞 H.F) ↔ w' = w ∨ IsConjPl H w w' := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  rw [Chr.under_eq_iff_conjPl c hcm.rank hcm.ne, isConjPl_iff_conjPl]
  have e : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  rw [e]

theorem under_mem {p : ℕ} {w : PlE H} : w.under (𝓞 H.F) ∈ placesOver H.F p ↔ w ∈ placesOver H.E p := by
  show algebraMap (𝓞 H.F) (𝓞 H.E) ((p : ℕ) : 𝓞 H.F) ∈ w.asIdeal ↔ _
  rw [map_natCast]
  rfl

theorem exists_under (v : HeightOneSpectrum (𝓞 H.F)) : ∃ w : PlE H, w.under (𝓞 H.F) = v := by
  have := v.isPrime
  obtain ⟨⟨W, hW, hWv⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 H.E)))
  exact ⟨⟨W, hW, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot W⟩, HeightOneSpectrum.ext hWv.over.symm⟩

theorem div_over (P : PiBar H) {k : Fin 2} {w : PlE H} (h : P.Div k w) : w ∈ placesOver H.E (H.g k) := by
  have h1 := P.pb_over k
  rw [← (show w.under (𝓞 H.K) = P.pb k from h)] at h1
  have h2 : algebraMap (𝓞 H.K) (𝓞 H.E) ((H.g k : ℕ) : 𝓞 H.K) ∈ w.asIdeal := h1
  rwa [map_natCast] at h2

theorem div_iff_not_div (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    {w w' : PlE H} (hw : w ∈ placesOver H.E (H.g k)) (h : IsConjPl H w w') : P.Div k w ↔ ¬ P.Div k w' :=
  ((Chr.splitsC_main R H (H.g k) (H.g_prime k) hs w hw).2.2.2 (P.pb k) (P.pb_over k) w'
    ((isConjPl_iff_conjPl w w').1 h)).2

theorem not_isConjPl (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    {w w' : PlE H} (hw : P.Div k w) (hw' : P.Div k w') : ¬ IsConjPl H w w' :=
  fun h => (div_iff_not_div P hs (div_over P hw) h).1 hw hw'

def below {p : ℕ} {I : Type} (pl : I → PlE H) (h : ∀ i, pl i ∈ placesOver H.E p) (i : I) : placesOver H.F p :=
  ⟨(pl i).under (𝓞 H.F), under_mem.2 (h i)⟩

theorem below_injective {p : ℕ} {I : Type} (pl : I → PlE H) (h : ∀ i, pl i ∈ placesOver H.E p)
    (h1 : Function.Injective pl) (h2 : ∀ i j, ¬ IsConjPl H (pl i) (pl j)) : Function.Injective (below pl h) :=
  fun i j e => ((under_eq_iff (pl j) (pl i)).1 (congrArg Subtype.val e)).elim (fun e => h1 e) fun e => absurd e (h2 j i)

theorem card_placesOver {p : ℕ} (hp : p.Prime) (hs : (placesOver H.E p).ncard = Module.finrank ℚ H.E) :
    Nat.card (placesOver H.F p) = R.f := by
  obtain ⟨e, h, h1, h2, h3⟩ := HalfPlaces.exists_places_cover H hp hs
  have hb : Function.Bijective (below e h) := by
    refine ⟨below_injective e h h1 h2, fun v => ?_⟩
    obtain ⟨w, hw⟩ := exists_under v.1
    obtain ⟨i, hi⟩ := h3 w (under_mem.1 (hw ▸ v.2))
    exact ⟨i, Subtype.ext (((under_eq_iff (e i) w).2 hi).symm.trans hw)⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem below_bijective {p : ℕ} (hp : p.Prime) (hs : (placesOver H.E p).ncard = Module.finrank ℚ H.E)
    {I : Type} [Fintype I] (hI : Fintype.card I = R.f) (pl : I → PlE H) (h : ∀ i, pl i ∈ placesOver H.E p)
    (h1 : Function.Injective pl) (h2 : ∀ i j, ¬ IsConjPl H (pl i) (pl j)) : Function.Bijective (below pl h) := by
  have hc := card_placesOver hp hs
  haveI : Finite (placesOver H.F p) := Nat.finite_of_card_ne_zero (hc ▸ (GaloisStage.f_pos R).ne')
  exact (Nat.bijective_iff_injective_and_card _).2
    ⟨below_injective pl h h1 h2, by rw [hc, Nat.card_eq_fintype_card, hI]⟩

theorem existsUnique_div (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : ∃! w : PlE H, P.Div k w ∧ w.under (𝓞 H.F) = v := by
  obtain ⟨w, hw⟩ := exists_under v.1
  have hex : ∃ w : PlE H, P.Div k w ∧ w.under (𝓞 H.F) = v := by
    by_cases h : P.Div k w
    · exact ⟨w, h, hw⟩
    · obtain ⟨w', hw', -⟩ := Chr.existsUnique_conjPl H.conj.toRingEquiv w
      have hc := (isConjPl_iff_conjPl w w').2 hw'
      refine ⟨w', ?_, ((under_eq_iff w w').2 (Or.inr hc)).trans hw⟩
      by_contra h'
      exact h ((div_iff_not_div P hs (under_mem.1 (hw ▸ v.2)) hc).2 h')
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ha, fun b hb => ?_⟩
  exact ((under_eq_iff a b).1 (hb.2.trans ha.2.symm)).elim id fun e => absurd e (not_isConjPl P hs ha.1 hb.1)

def above (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : PlE H := (existsUnique_div P hs v).choose

theorem above_div (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : P.Div k (above P hs v) := (existsUnique_div P hs v).choose_spec.1.1

theorem above_under (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : (above P hs v).under (𝓞 H.F) = v := (existsUnique_div P hs v).choose_spec.1.2

theorem above_injective (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    Function.Injective (above P hs) :=
  fun v v' e => Subtype.ext (by rw [← above_under P hs v, e, above_under])

end Places

section Labels

def labDat (g : ℕ) [Fact g.Prime] : LabelDatum g := (LabelModel.inhab g).some

variable {g : ℕ} [Fact g.Prime]

def charLab (L : LabelDatum g) (ω : (ZMod g)ˣ →* ℂˣ) : (ZMod g)ˣ :=
  Units.mk0 (GLp.Model.isCharLab_exists L ω).choose (GLp.Model.isCharLab_exists L ω).choose_spec.1

theorem isCharLab_charLab (L : LabelDatum g) (ω : (ZMod g)ˣ →* ℂˣ) : IsCharLab L ω (charLab L ω) :=
  (GLp.Model.isCharLab_exists L ω).choose_spec

theorem isCharLab_pow (L : LabelDatum g) (ω : (ZMod g)ˣ →* ℂˣ) (n : ℕ) :
    IsCharLab L (ω ^ n) ((charLab L ω ^ n : (ZMod g)ˣ) : ZMod g) := by
  refine ⟨Units.ne_zero _, fun u hu => ?_⟩
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow,
    (isCharLab_charLab L ω).2 u hu]

theorem orderOf_charLab (L : LabelDatum g) {ω : (ZMod g)ˣ →* ℂˣ} (h : Function.Injective ω) :
    orderOf (charLab L ω) = g - 1 := by
  obtain ⟨u, hu, ho⟩ := GLp.Model.exists_gen L
  let T : (ZMod g)ˣ →* ℂ := L.teich.comp ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom.comp (Units.coeHom _))
  have hT : Function.Injective T := fun a b e => Units.ext <| (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
    (L.teich_inj _ _ (by simp) (by simp) e)
  have e : T (charLab L ω) = (ω u : ℂ) := ((isCharLab_charLab L ω).2 u hu).symm
  rw [← orderOf_injective T hT, e, orderOf_units, orderOf_injective ω h, ho]

theorem thetaOf_of_isCharLab (L : LabelDatum g) {χ : (ZMod g)ˣ →* ℂˣ} {c : ZMod g} (hc : IsCharLab L χ c)
    (a : (ZMod g)ˣ) : thetaOf L 1 (algebraMap (ZMod g) _ c) (algebraMap (ZMod g) _ (a : ZMod g)) = ((χ a : ℂˣ) : ℂ) := by
  obtain ⟨u, hu, ho⟩ := GLp.Model.exists_gen L
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, ho, Nat.card_eq_fintype_card, ZMod.card_units]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, u ^ m = a := mem_powers_iff_mem_zpowers.2 (htop ▸ Subgroup.mem_top a)
  have hcp : (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c) ^ (g ^ 1 - 1) = 1 := by
    rw [← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one hc.1, map_one]
  rw [Units.val_pow_eq_pow_val, map_pow, hu, LabelModel.thetaOf_pow g L one_pos hcp, map_pow,
    Units.val_pow_eq_pow_val, hc.2 u hu]

end Labels

end GlobalTheory.Mem.TypePl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffRenameCayleyBlockSymbolEmbeddi
section
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory.CayleyBlock

namespace TopRename

variable {p q : ℕ} (hc : Fintype.card (Unit × Fin p × Fin q) = p * q)

def idx : Fin p × Fin q ≃ Fin (p * q) :=
  (Equiv.punitProd (Fin p × Fin q)).symm.trans (Fintype.equivFinOfCardEq hc)

theorem blockEmb_eq (x : Fin q × Fin p × Fin p) :
    blockEmb hc x = (idx hc (x.2.1, x.1), idx hc (x.2.2, x.1)) := rfl

theorem blockEmb_injective : Function.Injective (blockEmb hc) := by
  rintro ⟨b, i, j⟩ ⟨b', i', j'⟩ h
  simp only [blockEmb_eq, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨⟨e1, e2⟩, ⟨e3, -⟩⟩ := h
  subst e1 e2 e3
  rfl

def permOf (τ : Fin q → Equiv.Perm (Fin p)) : Equiv.Perm (Fin (p * q)) :=
  (idx hc).permCongr (Equiv.prodCongrLeft fun b => (τ b)⁻¹)

theorem permOf_apply' (τ : Fin q → Equiv.Perm (Fin p)) (j : Fin p) (b : Fin q) :
    permOf hc τ (idx hc (j, b)) = idx hc ((τ b)⁻¹ j, b) := by
  simp [permOf, Equiv.permCongr_apply]

theorem permOf_apply (τ : Fin q → Equiv.Perm (Fin p)) (i : Fin p) (b : Fin q) :
    permOf hc τ (idx hc (τ b i, b)) = idx hc (i, b) := by
  rw [permOf_apply']
  simp

theorem sign_permOf (τ : Fin q → Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign (permOf hc τ) : ℤˣ) : ℤ) = sgnProd τ := by
  simp [permOf, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_prodCongrLeft, sgnProd]

theorem permOf_injective : Function.Injective (permOf hc) := by
  intro τ τ' e
  funext b
  have h : ∀ j, (τ b)⁻¹ j = (τ' b)⁻¹ j := by
    intro j
    have := congrArg (fun w : Equiv.Perm (Fin (p * q)) => w (idx hc (j, b))) e
    simp only [permOf_apply'] at this
    exact congrArg Prod.fst ((idx hc).injective this)
  exact inv_inj.mp (Equiv.ext h)

theorem graph_apply' {n : ℕ} (g : Fin n → Fin n) (x y : Fin n) :
    (∑ a, Finsupp.single (a, g a) 1 : Fin n × Fin n →₀ ℕ) (x, y) = if g x = y then 1 else 0 := by
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single x (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
  simp [Finsupp.single_apply]

theorem graph_permOf (τ : Fin q → Equiv.Perm (Fin p)) :
    (∑ a, Finsupp.single (a, permOf hc τ a) 1 : Fin (p * q) × Fin (p * q) →₀ ℕ) =
      (blockGraph τ).mapDomain (blockEmb hc) := by
  rw [blockGraph, Finsupp.mapDomain_finsetSum]
  simp_rw [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single, blockEmb_eq]
  rw [← (idx hc).sum_comp, ← (Equiv.prodCongrLeft fun b => τ b).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
  simp [permOf_apply]

theorem mem_range_of_graph (w : Equiv.Perm (Fin (p * q))) (u : Fin q × Fin p × Fin p →₀ ℕ)
    (h : u.mapDomain (blockEmb hc) = ∑ a, Finsupp.single (a, w a) 1) : ∃ τ, permOf hc τ = w := by
  have hr : ∀ x : Fin p × Fin q, ((idx hc).symm (w (idx hc x))).2 = x.2 := by
    intro x
    have h0 : (∑ a, Finsupp.single (a, w a) 1 : Fin (p * q) × Fin (p * q) →₀ ℕ) (idx hc x, w (idx hc x)) ≠ 0 := by
      rw [graph_apply' (fun a => w a)]
      simp
    rw [← h] at h0
    by_contra hne
    apply h0
    apply Finsupp.mapDomain_notin_range
    rintro ⟨⟨b, i, j⟩, hy⟩
    rw [blockEmb_eq, Prod.mk.injEq] at hy
    apply hne
    have hx : x = (i, b) := ((idx hc).injective hy.1).symm
    rw [← hy.2, Equiv.symm_apply_apply, hx]
  let f : Fin q → Fin p → Fin p := fun b i => ((idx hc).symm (w (idx hc (i, b)))).1
  have hf : ∀ b, Function.Injective (f b) := by
    intro b i i' e
    have : (idx hc).symm (w (idx hc (i, b))) = (idx hc).symm (w (idx hc (i', b))) :=
      Prod.ext e ((hr (i, b)).trans (hr (i', b)).symm)
    simpa using this
  let σ : Fin q → Equiv.Perm (Fin p) := fun b => Equiv.ofBijective (f b) (Finite.injective_iff_bijective.mp (hf b))
  refine ⟨fun b => (σ b)⁻¹, ?_⟩
  ext1 a
  obtain ⟨⟨i, b⟩, rfl⟩ := (idx hc).surjective a
  rw [permOf_apply', inv_inv, ← (idx hc).apply_symm_apply (w (idx hc (i, b)))]
  congr 1
  exact Prod.ext rfl (hr (i, b)).symm

end TopRename


open TopRename in
theorem topCoeff_rename_blockEmb : ∀ {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q)
    (G : MvPolynomial (Fin q × Fin p × Fin p) ℂ), GlobalTheory.GoodMetric.topCoeff (rename (blockEmb h1) G) =
      ∑ τ : Fin q → Equiv.Perm (Fin p), (sgnProd τ : ℂ) * AddMonoidAlgebra.coeff G (blockGraph τ) := by
  intro p q h1 G
  rw [GlobalTheory.GoodMetric.topCoeff]
  symm
  refine Fintype.sum_of_injective (permOf h1) (permOf_injective h1) _ _ ?_ ?_
  · intro w hw
    rw [coeff_rename_eq_zero, mul_zero]
    intro u hu
    obtain ⟨τ, rfl⟩ := mem_range_of_graph h1 w u hu
    exact absurd ⟨τ, rfl⟩ hw
  · intro τ
    rw [graph_permOf, coeff_rename_mapDomain _ (blockEmb_injective h1), ← sign_permOf h1]

end GlobalTheory.CayleyBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CechPic
open scoped TensorProduct

namespace GlobalTheory.IntModel

theorem ringKrullDim_adjoin_le {R S : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.IsAlgebraic R S] (s : Finset S) :
    ringKrullDim (Algebra.adjoin R (s : Set S)) ≤ ringKrullDim R := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, Algebra.adjoin_empty]
    exact (ringKrullDim_eq_of_ringEquiv (Algebra.botEquivOfInjective
      (FaithfulSMul.algebraMap_injective R S)).toRingEquiv).le
  | insert a s _ ih =>
    refine le_trans ?_ ih
    set T := Algebra.adjoin R (s : Set S)
    set T' := Algebra.adjoin R ((insert a s : Finset S) : Set S)
    have hle : T ≤ T' := Algebra.adjoin_mono (by simp)
    have ha : a ∈ T' := Algebra.subset_adjoin (by simp)
    have : Algebra.FiniteType R T := (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset s)
    have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing R T
    let f : T →+* T' := (Subalgebra.inclusion hle).toRingHom
    have hf : Function.Injective f := Subalgebra.inclusion_injective hle
    have hgen : Function.Surjective (Polynomial.eval₂RingHom f ⟨a, ha⟩) := by
      rintro ⟨y, hy⟩
      induction hy using Algebra.adjoin_induction with
      | mem x hx =>
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hx) with rfl | hx
        · exact ⟨Polynomial.X, by simp⟩
        · exact ⟨Polynomial.C ⟨x, Algebra.subset_adjoin hx⟩, by simp [f]⟩
      | algebraMap r => exact ⟨Polynomial.C (algebraMap R T r), by simp [f]; rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨p, hp⟩ := hx
        obtain ⟨q, hq⟩ := hy
        exact ⟨p + q, by rw [map_add (f := _), hp, hq]; rfl⟩
      | mul x y _ _ hx hy =>
        obtain ⟨p, hp⟩ := hx
        obtain ⟨q, hq⟩ := hy
        exact ⟨p * q, by rw [map_mul, hp, hq]; rfl⟩
    obtain ⟨g, hg0, hg⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) a
    have hinj : Function.Injective (algebraMap R T) := fun x y h =>
      FaithfulSMul.algebraMap_injective R S (congrArg Subtype.val h)
    have halg : ∃ g : Polynomial T, g ≠ 0 ∧ Polynomial.eval₂ f ⟨a, ha⟩ g = 0 := by
      refine ⟨g.map (algebraMap R T), (Polynomial.map_ne_zero_iff hinj).2 hg0, Subtype.ext ?_⟩
      rw [Polynomial.eval₂_map]
      refine (Polynomial.hom_eval₂ g _ T'.val.toRingHom _).trans ?_
      exact hg
    refine (ringKrullDim_le_iff_height_le _).2 fun q hq => ?_
    have h := ReciprocityTheory.CA.height_le_height_comap_of_eval₂_surjective f hf _ hgen halg q
    exact le_trans (by exact_mod_cast h) (Ideal.height_le_ringKrullDim_of_ne_top (Ideal.comap_isPrime f q).ne_top)

theorem ringKrullDim_le_add {O A : Type} (K : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [CommRing A]
    [IsDomain A] [Algebra O A] [FaithfulSMul O A] [Algebra.FiniteType O A] [Field K] [Algebra O K] [IsFractionRing O K] :
    ringKrullDim A ≤ ringKrullDim O + ringKrullDim (K ⊗[O] A) := by
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast O (A := A)
  rw [ringKrullDim_genericFibre_eq O K hd]
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis O A
  have hc : Cardinal.mk s = d := hs.cardinalMk_eq_trdeg.trans hd
  have : Finite s := Cardinal.lt_aleph0_iff_finite.1 (hc ▸ Cardinal.natCast_lt_aleph0)
  let R := Algebra.adjoin O (Set.range ((↑) : s → A))
  have e : MvPolynomial s O ≃+* R := hs.1.aevalEquiv.toRingEquiv
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv _ e
  have : Algebra.IsAlgebraic R A := hs.isAlgebraic
  have : Algebra.FiniteType R A := .of_restrictScalars_finiteType O R A
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := R) (A := A)
  have h := ringKrullDim_adjoin_le (R := R) t
  rw [ht, ringKrullDim_eq_of_ringEquiv Subalgebra.topEquiv.toRingEquiv, ← ringKrullDim_eq_of_ringEquiv e,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ENat.card_eq_coe_natCard, ← Cardinal.toNat_mk, hc, Cardinal.toNat_natCast] at h
  exact h

theorem topologicalKrullDim_eq_succ {O K : Type} [CommRing O] [IsDedekindDomain O] (hO : ¬ IsField O) [Field K]
    [Algebra O K] [IsFractionRing O K] {X Y : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp O} [IsProper p] [Flat p]
    {j : Y ⟶ X} {q : Y ⟶ Sp K} (H : IsPullback j q p (spMap (algebraMap O K))) {d : ℕ}
    (hd : topologicalKrullDim Y = d) : topologicalKrullDim X = (d + 1 : ℕ) := by
  have hO1 : ringKrullDim O ≤ 1 := by exact_mod_cast Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 O)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨A, _, _, i, _, a, rfl, hi⟩ := exists_affine_chart_over p x
    obtain ⟨i₀, _, -⟩ := exists_affine_chart_of_isPullback H i hi
    refine ⟨Set.range i, i.isOpenEmbedding.isOpen_range, ⟨a, rfl⟩, ?_⟩
    rw [topologicalKrullDim_eq_of_isEmbedding i.isOpenEmbedding.isEmbedding rfl]
    have : Nonempty (Spec (.of A)) := ⟨a⟩
    have : IsIntegral (Spec (.of A)) := isIntegral_of_isOpenImmersion i
    have : IsDomain A := (affine_isIntegral_iff (.of A)).1 this
    have hft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap O A))) := by rw [← hi]; infer_instance
    have hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap O A))) := by rw [← hi]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
    rw [HasRingHomProperty.Spec_iff (P := @Flat)] at hfl
    have : Algebra.FiniteType O A := RingHom.finiteType_algebraMap.mp hft
    have : Module.Flat O A := RingHom.flat_algebraMap_iff.mp hfl
    have : FaithfulSMul O A := inferInstance
    have h₁ : ringKrullDim (K ⊗[O] A) ≤ d :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).ge.trans
        (i₀.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hd.le)
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).le.trans ((ringKrullDim_le_add (O := O) K).trans ?_)
    refine (add_le_add hO1 h₁).trans_eq ?_
    push_cast
    exact add_comm _ _
  · have := IsPreimmersion.of_isLocalization (R := O) (S := K) (nonZeroDivisors O)
    have : IsPreimmersion j := MorphismProperty.of_isPullback H.flip this
    have hj := j.isEmbedding
    have eX : topologicalKrullDim X = Order.krullDim X := Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
    have eY : topologicalKrullDim Y = Order.krullDim Y := Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
    rw [eY] at hd
    rw [eX]
    obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 hd.ge
    have hm : StrictMono (j : Y → X) := fun a b h =>
      ⟨hj.isInducing.specializes_iff.2 h.1, fun h' => h.2 (hj.isInducing.specializes_iff.1 h')⟩
    obtain ⟨m, hm0, hmp⟩ := Ring.not_isField_iff_exists_prime.1 hO
    have hp (y : Y) : (p (j y)).asIdeal = ⊥ := by
      rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
      change Ideal.comap (algebraMap O K) (q y).asIdeal = ⊥
      rw [(Ideal.eq_bot_or_top _).resolve_right (q y).2.ne_top]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
    have hs : p (j l.head) ⤳ (⟨m, hmp⟩ : PrimeSpectrum O) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 ((hp _).le.trans bot_le)
    obtain ⟨x, hx, hxm⟩ := p.isClosedMap.specializingMap hs
    have hlt : x < (l.map _ hm).head := by
      refine ⟨hx, fun h' => hm0 ?_⟩
      have h₁ : p x ⤳ p (j l.head) := Specializes.map h' p.continuous
      rw [hxm] at h₁
      have h₂ : m ≤ (p (j l.head)).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h₁
      exact le_bot_iff.1 (h₂.trans (hp _).le)
    refine Order.le_krullDim_iff.2 ⟨(l.map _ hm).cons x hlt, ?_⟩
    simp [hl]

theorem exists_flat_model {O K : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {Y : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ Sp K) (hq : IsProjOver q) {ι : Type} [Fintype ι]
    (P : ι → Scheme.{0}) (p : ∀ i, P i ⟶ Sp O) (f : ∀ i, Y ⟶ P i) (hp : ∀ i, IsProjOver (p i))
    (hf : ∀ i, f i ≫ p i = q ≫ spMap (algebraMap O K)) :
    ∃ (X : Scheme.{0}) (π : X ⟶ Sp O) (j : Y ⟶ X), IsIntegral X ∧ IsProjOver π ∧ Flat π ∧
      IsPullback j q π (spMap (algebraMap O K)) ∧ ∀ i, ∃ g : X ⟶ P i, j ≫ g = f i ∧ g ≫ p i = π := by
  obtain ⟨W₀, s₀, i₀, hs₀, H₀⟩ :=
    GlobalTheory.ProjClosure.exists_isProjOver_isPullback_of_isLocalization (nonZeroDivisors O) q hq
  obtain ⟨W, h, r, hW, hr, hg⟩ :=
    CommonModel.exists_common s₀ hs₀ i₀ P p f hp (fun i => (hf i).trans H₀.w.symm) Finset.univ
  have w : h ≫ r ≫ s₀ = q ≫ spMap (algebraMap O K) := by rw [← Category.assoc, hr, H₀.w]
  have hqp : IsProper q := CommonModel.isProper_of_isProjOver hq
  have hsp : IsProper (r ≫ s₀) := CommonModel.isProper_of_isProjOver hW
  have hb := IsPullback.of_hasPullback (r ≫ s₀) (spMap (algebraMap O K))
  let f' : Y ⟶ pullback (r ≫ s₀) (spMap (algebraMap O K)) := pullback.lift h q w
  have hf' : f' ≫ pullback.snd _ _ = q := pullback.lift_snd _ _ _
  let ρ : pullback (r ≫ s₀) (spMap (algebraMap O K)) ⟶ Y :=
    H₀.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
  have hρ : ρ ≫ q = pullback.snd _ _ := H₀.lift_snd _ _ _
  have hfρ : f' ≫ ρ = 𝟙 Y := by
    apply H₀.hom_ext
    · rw [Category.assoc, H₀.lift_fst, pullback.lift_fst_assoc, hr, Category.id_comp]
    · rw [Category.assoc, hρ, pullback.lift_snd, Category.id_comp]
  have : IsSeparated (ρ ≫ q) := by rw [hρ]; infer_instance
  have : IsSeparated ρ := IsSeparated.of_comp ρ q
  have : IsClosedImmersion (f' ≫ ρ) := by rw [hfρ]; infer_instance
  have : IsClosedImmersion f' := IsClosedImmersion.of_comp f' ρ
  have hh : f' ≫ pullback.fst _ _ = h := pullback.lift_fst _ _ _
  have : IsAffineHom (pullback.fst (r ≫ s₀) (spMap (algebraMap O K))) :=
    MorphismProperty.of_isPullback hb.flip (isAffineHom_of_isAffine _)
  have : QuasiCompact h := by rw [← hh]; infer_instance
  have : Flat (spMap (algebraMap O K)) := flat_specMap_localization (nonZeroDivisors O) K
  have : Mono (spMap (algebraMap O K)) := mono_specMap_localization (nonZeroDivisors O) K
  have hpb := isPullback_toImage_of_isClosedImmersion h f' _ hh
  refine ⟨h.image, h.imageι ≫ r ≫ s₀, h.toImage, inferInstance,
    ProjSpace.isProjOver_comp_of_isClosedImmersion _ hW, flat_image_of_over_fractionField h (r ≫ s₀) q w.symm, ?_,
    fun i => ?_⟩
  · have := hpb.flip.paste_vert hb
    rwa [hf'] at this
  · obtain ⟨g, h₁, h₂⟩ := hg i (Finset.mem_univ i)
    exact ⟨h.imageι ≫ g, by rw [← Category.assoc, h.toImage_imageι, h₁], by rw [Category.assoc, h₂]⟩

end GlobalTheory.IntModel
end
end

