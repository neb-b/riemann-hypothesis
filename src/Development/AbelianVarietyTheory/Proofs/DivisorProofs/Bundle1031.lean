module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBasisHyperbolicPlaneComplement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeEmbeddingMemUnitGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceLocalLatticeBasisHyperbolicPlane
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section

namespace GlobalTheory.PlaneSkewBasis

open GlobalTheory.AdelicU GlobalTheory.PlaneBasis

theorem exists_decomp {E : Type} [Field E] {n₁ : ℕ} (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E)
    (hind : ∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0)
    (z : Fin (n₁ + 2) → E) : ∃ (s t : E) (u : Fin n₁ → E), z = s • x + ι *ᵥ u + t • y := by
  let φ : (E × E) × (Fin n₁ → E) →ₗ[E] (Fin (n₁ + 2) → E) :=
    ((LinearMap.fst E E E).smulRight x).comp (LinearMap.fst E (E × E) (Fin n₁ → E)) +
      (Matrix.mulVecLin ι).comp (LinearMap.snd E (E × E) (Fin n₁ → E)) +
      ((LinearMap.snd E E E).smulRight y).comp (LinearMap.fst E (E × E) (Fin n₁ → E))
  have hφ : ∀ p, φ p = p.1.1 • x + ι *ᵥ p.2 + p.1.2 • y := fun p => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨s, t⟩, u⟩ h
    rw [hφ] at h
    obtain ⟨rfl, rfl, rfl⟩ := hind s t u h
    rfl
  have hdim : Module.finrank E ((E × E) × (Fin n₁ → E)) = Module.finrank E (Fin (n₁ + 2) → E) := by
    simp [Module.finrank_prod]; omega
  obtain ⟨p, hp⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj z
  exact ⟨p.1.1, p.1.2, p.2, by rw [← hp, hφ]⟩

theorem exists_isSplitBasis_plane_of_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] Fv F v) (n₁ : ℕ) (L : Submodule (𝓞 E) (Fin (n₁ + 2) → E))
    (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E) (β₁ : GL (Fin n₁) (Fv F v)) (i₀ i₁ : ℕ),
    i₀ < i₁ → i₁ < n₁ + 2 →
    (∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) →
    (∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0) →
    PrimAt (GlobalTheory.AdelicU.splitPrime τ) L x → PrimAt (GlobalTheory.AdelicU.splitPrime τ) L y → GlobalTheory.AdelicU.IsSplitBasis τ (lowLat ι L) β₁ →
    ∃ β : GL (Fin (n₁ + 2)) (Fv F v), GlobalTheory.AdelicU.IsSplitBasis τ L β ∧ ∀ i : Fin (n₁ + 2),
      (i.1 = i₀ → ∀ r, β.1 r i = τ (x r)) ∧ (i.1 = i₁ → ∀ r, β.1 r i = τ (y r)) ∧
      ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map τ * β₁.1) r j := by
  intro F E _ _ _ _ _ σ _ v τ n₁ L x y ι β₁ i₀ i₁ h01 h1n hdec hind hxP hyP hβ₁
  have hx : (∀ c : E, c • x ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ c) = 1 := by
    simp only [valued_apply_eq_valuation]; exact hxP
  have hy : (∀ c : E, c • y ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ c) = 1 := by
    simp only [valued_apply_eq_valuation]; exact hyP
  have hO : ∀ a : v.adicCompletion F, a ∈ v.adicCompletionIntegers F ↔ Valued.v a ≤ 1 := fun a =>
    HeightOneSpectrum.mem_adicCompletionIntegers _ _ _
  set M := colMat τ x y ι β₁.1 i₀ i₁ with hM
  set P := Submodule.span (v.adicCompletionIntegers F) (Set.range fun i r => M r i) with hP
  set Q := LinearMap.range M.mulVecLin with hQ
  have hsmul : ∀ (c : E) (z : Fin (n₁ + 2) → E), (fun r => τ ((c • z) r)) = τ c • fun r => τ (z r) :=
    fun c z => funext fun r => by simp
  have hτmul : ∀ u : Fin n₁ → E, (fun r => τ ((ι *ᵥ u) r)) = ι.map τ *ᵥ fun r => τ (u r) :=
    fun u => funext fun r => by simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hc0 : (fun r => M r ⟨i₀, by omega⟩) = fun r => τ (x r) := funext fun r => by simp [hM, colMat]
  have hc1 : (fun r => M r ⟨i₁, h1n⟩) = fun r => τ (y r) := funext fun r => by
    simp [hM, colMat, h01.ne']
  have hcj : ∀ j : Fin n₁, (fun r => M r ⟨skip i₀ i₁ j, skip_lt j.2⟩) = fun r => (ι.map τ * β₁.1) r j :=
    fun j => funext fun r => by
      simp [hM, colMat, skip_ne_left h01, skip_ne_right h01, unskip_skip h01, j.2]
  have hPx : (fun r => τ (x r)) ∈ P := hc0 ▸ Submodule.subset_span ⟨_, rfl⟩
  have hPy : (fun r => τ (y r)) ∈ P := hc1 ▸ Submodule.subset_span ⟨_, rfl⟩
  have hPcol : ∀ j : Fin n₁, (fun r => (ι.map τ * β₁.1) r j) ∈ P := fun j =>
    hcj j ▸ Submodule.subset_span ⟨_, rfl⟩
  have hcolsum : ∀ w₁ : Fin n₁ → v.adicCompletion F,
      (ι.map τ * β₁.1) *ᵥ w₁ = ∑ j, w₁ j • (fun r => (ι.map τ * β₁.1) r j) := by
    intro w₁; funext r; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hPimg : ∀ w₁ : Fin n₁ → v.adicCompletion F, (∀ j, w₁ j ∈ v.adicCompletionIntegers F) →
      (ι.map τ * β₁.1) *ᵥ w₁ ∈ P := by
    intro w₁ hw
    rw [hcolsum]
    exact sum_mem fun j _ => smul_mem_int (hw j) (hPcol j)
  have hQcolv : ∀ i, (fun r => M r i) ∈ Q := fun i =>
    ⟨Pi.single i 1, funext fun r => by simp [Matrix.mulVec_single_one, Matrix.transpose_apply]⟩
  have hQx : (fun r => τ (x r)) ∈ Q := hc0 ▸ hQcolv _
  have hQy : (fun r => τ (y r)) ∈ Q := hc1 ▸ hQcolv _
  have hQimg : ∀ w₁ : Fin n₁ → v.adicCompletion F, (ι.map τ * β₁.1) *ᵥ w₁ ∈ Q := by
    intro w₁
    rw [hcolsum]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (hcj j ▸ hQcolv _)
  have hsplit : ∀ (s t : E) (u : Fin n₁ → E), (fun r => τ ((s • x + ι *ᵥ u + t • y) r)) = τ s • (fun r => τ (x r)) +
      (ι.map τ * β₁.1) *ᵥ ((β₁⁻¹).1 *ᵥ fun r => τ (u r)) + τ t • fun r => τ (y r) := by
    intro s t u
    have e : (fun r => τ (u r)) = β₁.1 *ᵥ ((β₁⁻¹).1 *ᵥ fun r => τ (u r)) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, ← e, ← hτmul, ← hsmul, ← hsmul]; funext r; simp
  have hSub : ∀ z ∈ L, (fun r => τ (z r)) ∈ P := by
    intro z hz
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hdec z hz
    have hu' : u ∈ lowLat ι L := hu
    have h1 := (hβ₁ ((β₁⁻¹).1 *ᵥ fun r => τ (u r))).2 (by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact tau_mem_splitLat τ hu')
    rw [hsplit]
    exact add_mem (add_mem (smul_mem_int ((hO _).2 (hx.1 s hs)) hPx) (hPimg _ h1))
      (smul_mem_int ((hO _).2 (hy.1 t ht)) hPy)
  have hImg : ∀ u ∈ splitLat τ (lowLat ι L), ι.map τ *ᵥ u ∈ splitLat τ L := fun u hu =>
    splitLat_induction τ _ (p := fun u => ι.map τ *ᵥ u ∈ splitLat τ L)
      (fun a ha z hz => by
        rw [Matrix.mulVec_smul, ← hτmul]; exact smul_mem_int ha (tau_mem_splitLat τ hz))
      (by rw [Matrix.mulVec_zero]; exact zero_mem _)
      (fun u w hu hw => by rw [Matrix.mulVec_add]; exact add_mem hu hw)
      (fun u hu => by rw [Matrix.mulVec_neg]; exact neg_mem hu) hu
  have hunit : ∀ z : Fin (n₁ + 2) → E, ((∀ c : E, c • z ∈ L → Valued.v (τ c) ≤ 1) ∧
      ∃ c : E, c • z ∈ L ∧ Valued.v (τ c) = 1) → (fun r => τ (z r)) ∈ splitLat τ L := by
    rintro z ⟨-, c, hc, hv⟩
    have hne : τ c ≠ 0 := by intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
    have h2 := tau_mem_splitLat τ hc
    rw [hsmul] at h2
    have hinv : (τ c)⁻¹ ∈ v.adicCompletionIntegers F := (hO _).2 (by rw [map_inv₀, hv, inv_one])
    have := smul_mem_int hinv h2
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hColSL : ∀ i, (fun r => M r i) ∈ splitLat τ L := by
    intro i
    by_cases h0 : i.1 = i₀
    · convert hunit x hx using 1; funext r; simp [hM, colMat, h0]
    by_cases h1 : i.1 = i₁
    · convert hunit y hy using 1; funext r; simp only [hM, colMat, if_neg h0, if_pos h1]
    by_cases h2 : unskip i₀ i₁ i.1 < n₁
    · have : (fun r => M r i) = ι.map τ *ᵥ (β₁.1 *ᵥ Pi.single ⟨_, h2⟩ 1) := by
        funext r
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
        simp only [hM, colMat, if_neg h0, if_neg h1, dif_pos h2, Matrix.transpose_apply]
        rfl
      rw [this]
      refine hImg _ ((hβ₁ _).1 fun k => ?_)
      rw [Pi.single_apply]; split_ifs
      exacts [one_mem _, zero_mem _]
    · convert zero_mem (splitLat τ L) using 1; funext r; simp [hM, colMat, h0, h1, h2]
  have hPle : P ≤ splitLat τ L := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hColSL i)
  have hSLle : ∀ u ∈ splitLat τ L, u ∈ P := fun u hu =>
    splitLat_induction τ L (p := (· ∈ P)) (fun a ha z hz => smul_mem_int ha (hSub z hz)) (zero_mem _)
      (fun _ _ => add_mem) (fun _ => neg_mem) hu
  have hR : ∀ z : Fin (n₁ + 2) → E, (fun r => τ (z r)) ∈ Q := by
    intro z
    obtain ⟨s, t, u, rfl⟩ := exists_decomp x y ι hind z
    rw [hsplit]
    exact add_mem (add_mem (Submodule.smul_mem _ _ hQx) (hQimg _)) (Submodule.smul_mem _ _ hQy)
  have hsurj : Function.Surjective M.mulVec := by
    intro u
    have : u ∈ Q := by
      rw [← Finset.univ_sum_single u]
      refine sum_mem fun k _ => ?_
      have e : Pi.single k (u k) = u k • fun r => τ ((Pi.single k (1 : E) : Fin (n₁ + 2) → E) r) := by
        funext r
        by_cases h : r = k
        · subst h; simp
        · simp [h]
      rw [e]
      exact Submodule.smul_mem _ _ (hR _)
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw⟩
  have hU : IsUnit M := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  refine ⟨hU.unit, ?_, fun i => ⟨?_, ?_, ?_⟩⟩
  · intro u
    rw [IsUnit.unit_spec]
    constructor
    · intro hu; exact hPle (mem_colSpan.2 ⟨u, hu, rfl⟩)
    · intro hu
      obtain ⟨w, hw, e⟩ := mem_colSpan.1 (hSLle _ hu)
      have := Matrix.mulVec_injective_iff_isUnit.2 hU e
      rw [← this]; exact hw
  · intro h r; rw [IsUnit.unit_spec]; simp [hM, colMat, h]
  · intro h r; rw [IsUnit.unit_spec]; simp [hM, colMat, h, h01.ne']
  · intro j h r
    rw [IsUnit.unit_spec]
    have : i = ⟨skip i₀ i₁ j, skip_lt j.2⟩ := Fin.ext h
    subst this
    exact congrFun (hcj j) r

end GlobalTheory.PlaneSkewBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDdREqOfEquiv
section
open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

open Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.ConjCrys

section DdR

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem ddR_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ DdR PD ρ, GlobalTheory.HTW.SumJumps.ext1 Qp BdR f x ∈ DdR PD ρ' := by
  intro x hx
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  have := hx g
  unfold actVdR at this ⊢
  rw [GlobalTheory.HTW.SumJumps.ext1_comm f (ρ g) (ρ' g) (hf g), this]

theorem finrank_ddR_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    finrank LL (DdR PD ρ) = finrank LL (DdR PD ρ') :=
  GlobalTheory.HTW.Rec.finrank_eq_of_equiv_tensor e _ _ (ddR_map PD e.toLinearMap he)
    (ddR_map PD e.symm.toLinearMap (GlobalTheory.HTW.Rec.symm_equivariant e he))

end DdR

section Matrix

theorem mapRep_conj {Γ : Type} [Group Γ] {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (f : R →+* S)
    (M : GL (Fin a) R) (ρ : Γ →* GL (Fin a) R) :
    mapRep f ((MulAut.conj M).toMonoidHom.comp ρ) =
      (MulAut.conj (Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) R →+* Matrix (Fin a) (Fin a) S).toMonoidHom M)).toMonoidHom.comp
        (mapRep f ρ) := by
  ext g : 1
  simp [mapRep, MulAut.conj_apply, map_mul, map_inv]

variable {l : ℕ} [Fact l.Prime]

def glOf {n : ℕ} (L : FinExt l) (A : GL (Fin n) (Om l))
    (hA : ∀ i j, (A : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1 ∧
      ((A⁻¹ : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1) : GL (Fin n) ↥L.1 where
  val := Matrix.of fun i j => ⟨_, (hA i j).1⟩
  inv := Matrix.of fun i j => ⟨_, (hA i j).2⟩
  val_inv := by
    apply Matrix.map_injective (f := (algebraMap ↥L.1 (Om l))) (algebraMap ↥L.1 (Om l)).injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact A.mul_inv
  inv_val := by
    apply Matrix.map_injective (f := (algebraMap ↥L.1 (Om l))) (algebraMap ↥L.1 (Om l)).injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact A.inv_mul

theorem map_glOf {n : ℕ} (L : FinExt l) (A : GL (Fin n) (Om l))
    (hA : ∀ i j, (A : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1 ∧
      ((A⁻¹ : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) i j ∈ L.1) :
    Units.map ((algebraMap ↥L.1 (Om l)).mapMatrix :
      Matrix (Fin n) (Fin n) ↥L.1 →+* Matrix (Fin n) (Fin n) (Om l)).toMonoidHom (glOf L A hA) = A := by
  ext i j
  rfl

end Matrix

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  (Bw : LocBridge l E Ω Gw O) {m : ℕ}

def linOf {L : Type} [Field L] (M : GL (Fin m) L) : (Fin m → L) ≃ₗ[L] (Fin m → L) :=
  LinearEquiv.ofLinear (Matrix.toLin' (M : Matrix (Fin m) (Fin m) L))
    (Matrix.toLin' ((M⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L))
    (by rw [← Matrix.toLin'_mul, M.mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, M.inv_mul, Matrix.toLin'_one])

theorem linOf_repE (L : FinExt l) (M : GL (Fin m) ↥L.1) (r : ↥Gw →* GL (Fin m) ↥L.1) (g) (v : Fin m → ↥L.1) :
    linOf M (Bw.repE L ((MulAut.conj M⁻¹).toMonoidHom.comp r) g v) = Bw.repE L r g (linOf M v) := by
  simp only [linOf, LocBridge.repE, LinearEquiv.ofLinear_apply, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.coeHom_apply, Matrix.toLin'_apply, inv_inv, Units.val_mul]
  erw [Matrix.toLinAlgEquiv'_apply, Matrix.toLinAlgEquiv'_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, M.mul_inv, Matrix.one_mul]

theorem local_conj (L : FinExt l) (M : GL (Fin m) ↥L.1) (r : ↥Gw →* GL (Fin m) ↥L.1) :
    (Bw.IsCrysE P L r → Bw.IsCrysE P L ((MulAut.conj M⁻¹).toMonoidHom.comp r)) ∧
    (Bw.IsdRE P L r → Bw.IsdRE P L ((MulAut.conj M⁻¹).toMonoidHom.comp r)) ∧
    ∀ τ a, Bw.multE P L ((MulAut.conj M⁻¹).toMonoidHom.comp r) τ a = Bw.multE P L r τ a := by
  have he := linOf_repE Bw L M r
  refine ⟨fun h => GlobalTheory.HTW.Rec.isCrys_of_equiv _ (linOf M) he h, fun h => ?_, fun τ a =>
    GlobalTheory.HTW.Rec.multV_eq_of_equiv _ (linOf M) he τ a⟩
  unfold LocBridge.IsdRE at h ⊢
  rw [finrank_ddR_eq_of_equiv _ (linOf M) he, h]

variable {P Bw}

theorem exists_conj_model {r : ↥Gw →* GL (Fin m) (Om l)} (A : GL (Fin m) (Om l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1)
    {LL' : FinExt l} {r' : ↥Gw →* GL (Fin m) ↥LL'.1} (hm : GlobalTheory.Pst.IsModel Bw r LL' r') :
    ∃ (h : LL'.1 ≤ (GlobalTheory.Pst.supExt LL' K).1) (M : GL (Fin m) ↥(GlobalTheory.Pst.supExt LL' K).1),
      GlobalTheory.Pst.IsModel Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) (GlobalTheory.Pst.supExt LL' K)
        ((MulAut.conj M⁻¹).toMonoidHom.comp (mapRep (IntermediateField.inclusion h).toRingHom r')) := by
  have h1 : LL'.1 ≤ (GlobalTheory.Pst.supExt LL' K).1 := le_sup_left
  have h2 : K.1 ≤ (GlobalTheory.Pst.supExt LL' K).1 := le_sup_right
  have hA' : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ (GlobalTheory.Pst.supExt LL' K).1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ (GlobalTheory.Pst.supExt LL' K).1 :=
    fun i j => ⟨h2 (hA i j).1, h2 (hA i j).2⟩
  have hm2 := hm.enlarge h1
  refine ⟨h1, glOf _ A hA', hm2.1, ?_⟩
  rw [mapRep_conj, hm2.2, map_inv, map_glOf]

theorem isCrysAt_conj {r : ↥Gw →* GL (Fin m) (Om l)} (A : GL (Fin m) (Om l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1)
    (hr : GlobalTheory.Pst.IsCrysAt P Bw r) : GlobalTheory.Pst.IsCrysAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) := by
  obtain ⟨LL', r', hm, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := exists_conj_model A K hA hm
  exact ⟨_, _, hM, (local_conj P Bw _ M _).1 ((GlobalTheory.Pst.local_ext P Bw h r').1.2 hc)⟩

theorem isJumpsAt_conj {r : ↥Gw →* GL (Fin m) (Om l)} (A : GL (Fin m) (Om l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Om l)) : Matrix (Fin m) (Fin m) (Om l)) i j ∈ K.1)
    {τ : E →+* Om l} {J : Multiset ℤ}
    (hr : GlobalTheory.Pst.IsJumpsAt P Bw r τ J) : GlobalTheory.Pst.IsJumpsAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) τ J := by
  obtain ⟨LL', r', hm, hdR, τ', hI, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := exists_conj_model A K hA hm
  obtain ⟨-, hdR2, -, hmult⟩ := GlobalTheory.Pst.local_ext P Bw h r'
  obtain ⟨-, hdR3, hmult3⟩ := local_conj P Bw _ M (mapRep (IntermediateField.inclusion h).toRingHom r')
  refine ⟨_, _, hM, hdR3 (hdR2.2 hdR), (IntermediateField.inclusion h).comp τ', fun x => hI x, fun n => ?_⟩
  rw [hc n, hmult3, hmult]

end Local

end GlobalTheory.ConjCrys


open GlobalTheory.ConjCrys in
theorem GlobalTheory.crysWith_conj : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (A : GL (Fin n) (PadicAlgCl l)) (K : FinExt l) (Jm : (E →+* PadicAlgCl l) → Multiset ℤ), (∀ i j, (A : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K.1 ∧ ((A⁻¹ : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K.1) → CrysWith r Jm → CrysWith ((MulAut.conj A⁻¹).toMonoidHom.comp r) Jm := by
  intro E Ω _ _ _ _ _ l _ n r A K Jm hA hr
  obtain ⟨hcont, hloc⟩ := hr
  refine ⟨?_, fun P AI hT w B hB O _ _ _ Bw hInd => ?_⟩
  · change Continuous fun g => A⁻¹ * r g * A⁻¹⁻¹
    exact (continuous_const.mul hcont).mul continuous_const
  · obtain ⟨h1, h2⟩ := hloc P AI hT w B hB O Bw hInd
    have e : ((MulAut.conj A⁻¹).toMonoidHom.comp r).comp (Dec (F := E) B).subtype =
        (MulAut.conj A⁻¹).toMonoidHom.comp (r.comp (Dec (F := E) B).subtype) := MonoidHom.comp_assoc _ _ _
    rw [e]
    refine ⟨isCrysAt_conj (r := r.comp (Dec (F := E) B).subtype) A K hA h1, fun τ LL' τ' hI => ?_⟩
    exact isJumpsAt_conj (r := r.comp (Dec (F := E) B).subtype) A K hA (h2 τ LL' τ' hI)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSmulMemAdelesFiniteMultipleOfTensorCongru
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend.TraceCE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def trAF : AF F ⊗[F] E →ₗ[AF F] AF F :=
  (Algebra.TensorProduct.rid F (AF F) (AF F)).toLinearMap ∘ₗ (Algebra.trace F E).baseChange (AF F)

theorem trAF_tmul (s : AF F) (e : E) :
    trAF (s ⊗ₜ[F] e) = algebraMap F (AF F) (Algebra.trace F E e) * s := by
  simp [trAF, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

theorem gen_eq (s : AF F) (o : 𝓞 E) :
    algebraMap (AF F) (AF F ⊗[F] E) s * incAF F E o = s ⊗ₜ[F] (o : E) := by
  show (s ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] (o : E)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem intF_zero : (0 : AF F) ∈ intF F 1 := ⟨0, fun _ => zero_mem _, by rw [one_smul]; rfl⟩

theorem intF_add {x y : AF F} (hx : x ∈ intF F 1) (hy : y ∈ intF F 1) : x + y ∈ intF F 1 := by
  obtain ⟨c, hc, e⟩ := hx
  obtain ⟨d, hd, e'⟩ := hy
  refine ⟨c + d, fun v => add_mem (hc v) (hd v), ?_⟩
  rw [one_smul] at e e' ⊢
  show x.2 + y.2 = c + d
  rw [e, e']

theorem intF_neg {x : AF F} (hx : x ∈ intF F 1) : -x ∈ intF F 1 := by
  obtain ⟨c, hc, e⟩ := hx
  refine ⟨-c, fun v => neg_mem (hc v), ?_⟩
  rw [one_smul] at e ⊢
  show -x.2 = -c
  rw [e]

theorem intF_algebraMap (t : 𝓞 F) : algebraMap F (AF F) (t : F) ∈ intF F 1 :=
  ⟨algebraMap F (Af F) (t : F), fun v => HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v t,
    by rw [one_smul]; rfl⟩

theorem trAF_mem_of_mem_SE {z : AF F ⊗[F] E} (hz : z ∈ SE F E) : trAF z ∈ intF F 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, hs, o, rfl⟩ := hg
    rw [gen_eq, trAF_tmul]
    have hi : IsIntegral ℤ (Algebra.trace F E (o : E)) := Algebra.isIntegral_trace o.2
    exact intF_one_mul (intF_algebraMap (⟨_, hi⟩ : 𝓞 F)) hs
  | zero => rw [map_zero]; exact intF_zero
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact intF_add ha hb
  | neg a _ ha => rw [map_neg]; exact intF_neg ha

theorem trAF_algebraMap (x : AF F) :
    trAF (algebraMap (AF F) (AF F ⊗[F] E) x) = Module.finrank F E • x := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, trAF_tmul]
  have h : Algebra.trace F E 1 = (Module.finrank F E : F) := by
    simpa using Algebra.trace_algebraMap (R := F) (S := E) (1 : F)
  rw [h, map_natCast, nsmul_eq_mul]

theorem finrank_smul_mem_intF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (x : AF F),
    algebraMap (AF F) (AF F ⊗[F] E) x ∈ CE F E N → Module.finrank F E • x ∈ intF F N := by
  intro F E _ _ _ _ _ N x h
  obtain ⟨s, hs, e⟩ := mem_CE.1 h
  have h1 := trAF_algebraMap (E := E) x
  rw [← e, map_nsmul] at h1
  obtain ⟨c, hc, ec⟩ := trAF_mem_of_mem_SE hs
  refine ⟨c, hc, ?_⟩
  rw [← h1]
  rw [one_smul] at ec
  rw [← ec]
  rfl

end GlobalTheory.HeckeExtend.TraceCE

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGramComp
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.RestrictNorm

theorem hasGram_comp {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (N : (K →+* ℂ) → V → ℝ) (φ : W →ₗ[K] V) (hφ : Function.Injective φ) {n : ℕ}
    (b : Module.Basis (Fin n) K V) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hG : IsGram b X N) :
    HasGram (fun σ (x : W) => N σ (φ x)) := by
  haveI : Module.Finite K V := Module.Finite.of_basis b
  let e : W ≃ₗ[K] LinearMap.range φ := LinearEquiv.ofInjective φ hφ
  let c := Module.finBasis K (LinearMap.range φ)
  obtain ⟨Y, hY, hn⟩ := GlobalTheory.Mem.DivInhab.exists_frames_restrict b X (fun v => (hG v).1) (LinearMap.range φ) c
  refine IsGram.hasGram (b := c.map e.symm) (X := Y) fun v => ⟨hY v, fun x => ?_⟩
  have h1 : Formalism.HermitianLatticesTheory.normAt (c.map e.symm) Y v x = Formalism.HermitianLatticesTheory.normAt c Y v (e x) := by
    have hv : Formalism.HermitianLatticesTheory.vecAt (c.map e.symm) v x = Formalism.HermitianLatticesTheory.vecAt c v (e x) := by
      funext i
      simp only [Formalism.HermitianLatticesTheory.vecAt, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm]
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    rw [hv]
  rw [h1, hn, (hG v).2]
  rfl

theorem restrict_deg : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (N : (K →+* ℂ) → V → ℝ) (φ : W →ₗ[K] V), Function.Injective φ → HasGram N → HasGram (fun σ (x : W) => N σ (φ x)) ∧ ∀ L : Submodule (𝓞 K) W, L.FG → Formalism.HN.rkK (L.map (φ.restrictScalars (𝓞 K))) = Formalism.HN.rkK L ∧ deg N (L.map (φ.restrictScalars (𝓞 K))) = deg (fun σ (x : W) => N σ (φ x)) L := by
  intro K V _ _ _ _ _ _ _ W _ _ _ _ N φ hφ hN
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  have hN' := hasGram_comp N φ hφ b X hG
  refine ⟨hN', fun L hL => ?_⟩
  obtain ⟨⟨m, ⟨c, Y⟩, hG'⟩⟩ := hN'
  letI : StarRing K := starRingOfComm
  have hr := Formalism.HN.rerealize K W (Fin m) V (Fin n) c Y b X φ (fun v => (hG' v).1) (fun v => (hG v).1) hφ
    (fun v x => by rw [(hG v).2, (hG' v).2]) L hL
  have hrk : Formalism.HN.rkK (L.map (φ.restrictScalars (𝓞 K))) = Formalism.HN.rkK L := by
    unfold Formalism.HN.rkK
    have hs : Submodule.span K ((L.map (φ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) =
        (Submodule.span K (L : Set W)).map φ := by
      rw [Submodule.map_coe, ← Submodule.span_image]
      rfl
    rw [hs]
    exact (Submodule.equivMapOfInjective φ hφ _).finrank_eq.symm
  refine ⟨hrk, ?_⟩
  unfold GlobalTheory.AllWt.deg GlobalTheory.AllWt.slope
  rw [hrk, slope_sq_eq hG (hL.map _), slope_sq_eq hG' hL]
  unfold Formalism.HN.muDef
  rw [hr.2.2.1]

end GlobalTheory.RestrictNorm
end
end

