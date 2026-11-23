module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstantCoeffTaylor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0089
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedExtFixedFieldFrobeniusPowDegree
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.UnrDeg

theorem det_pow_ne_zero {k F : Type} [Field k] [Field F] [Algebra k F] (τ : F ≃ₐ[k] F) {n : ℕ}
    (hord : orderOf τ = n) (bas : Module.Basis (Fin n) k F) :
    (Matrix.of fun i j : Fin n => (τ ^ (j : ℕ)) (bas i)).det ≠ 0 := by
  intro h
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  let L : F →ₗ[k] F :=
    { toFun := fun x => ∑ j : Fin n, u j * (τ ^ (j : ℕ)) x
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_smul_comm]
        congr 1
        exact (τ ^ (j : ℕ)).toLinearEquiv.map_smul r x }
  have hL : L = 0 := by
    refine bas.ext fun i => ?_
    have := congrFun hu i
    simpa [L, Matrix.mulVec, dotProduct, mul_comm] using this
  let f : Fin n → (F →* F) := fun j => ((τ ^ (j : ℕ)).toRingEquiv : F ≃+* F).toMonoidHom
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : τ ^ (i : ℕ) = τ ^ (j : ℕ) := AlgEquiv.ext fun x => DFunLike.congr_fun hij x
    have hi : (i : ℕ) ∈ Set.Iio (orderOf τ) := by rw [hord]; exact i.2
    have hj : (j : ℕ) ∈ Set.Iio (orderOf τ) := by rw [hord]; exact j.2
    exact Fin.ext (pow_injOn_Iio_orderOf hi hj h1)
  have li := (linearIndependent_monoidHom F F).comp f hf
  rw [Fintype.linearIndependent_iff] at li
  apply hu0
  funext j
  refine li u ?_ j
  funext x
  have := LinearMap.congr_fun hL x
  simpa [L, f, Finset.sum_apply, smul_eq_mul] using this

variable {l : ℕ} [Fact l.Prime]

def sig (l : ℕ) [Fact l.Prime] : ↥(MaximalUnramifiedExtension l) ≃ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) :=
  AlgEquiv.ofBijective (frobUr l) frobUr_bijective

theorem fr_apply (k : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : fr l k c = (frobUr l ^ k) c := rfl

theorem sig_pow (k : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : (sig l ^ k) c = fr l k c := by
  rw [fr_apply]
  induction k generalizing c with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgHom.mul_apply, ih]; rfl

end GlobalTheory.PMon.UnrDeg

namespace GlobalTheory.PMon.UnrDeg

theorem exists_moved (l : ℕ) [hl : Fact l.Prime] {r k : ℕ} (hk0 : 0 < k) (hkr : k < r) :
    ∃ c : ↥(MaximalUnramifiedExtension l), fr l r c = c ∧ fr l k c ≠ c := by
  have h2 := hl.out.two_le
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hls : l ^ k ≤ l ^ s := Nat.pow_le_pow_right (by omega) (by omega)
  have hl1 : l ^ 1 ≤ l ^ k := Nat.pow_le_pow_right (by omega) hk0
  rw [pow_one] at hl1
  have h5 : l ^ s * 2 ≤ l ^ s * l := Nat.mul_le_mul_left _ h2
  have hps : l ^ (s + 1) = l ^ s * l := pow_succ _ _
  have hN0 : 0 < l ^ (s + 1) - 1 := by omega
  have hkN : l ^ k < l ^ (s + 1) - 1 := by omega
  have h1N : 1 < l ^ (s + 1) - 1 := by omega
  have hd : ¬ l ∣ l ^ (s + 1) - 1 := fun h => hl.out.one_lt.ne' (Nat.dvd_one.mp
    ((Nat.dvd_sub_iff_right (by omega) (dvd_pow_self l (by omega))).mp h))
  haveI : NeZero (l ^ (s + 1) - 1) := ⟨hN0.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ (s + 1) - 1)
  have hmem : z ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨_, hN0, hd, hz.pow_eq_one⟩
  have h1 : (⟨z, hmem⟩ : ↥(MaximalUnramifiedExtension l)) ^ (l ^ (s + 1) - 1) = 1 := Subtype.ext hz.pow_eq_one
  refine ⟨⟨z, hmem⟩, ?_, fun h => ?_⟩
  · rw [fr_apply, frobUr_pow_root _ _ _ hN0 hd h1, show l ^ (s + 1) = (l ^ (s + 1) - 1) + 1 by omega, pow_succ, h1,
      one_mul]
  · rw [fr_apply, frobUr_pow_root _ _ _ hN0 hd h1] at h
    have h6 : z ^ l ^ k = z ^ 1 := by rw [pow_one]; exact congrArg Subtype.val h
    have := hz.pow_inj hkN h1N h6
    omega

theorem fixed_field_deg : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (E : FinExt l) (ω : Fin r → ↥(MaximalUnramifiedExtension l)),
    E.1 ≤ MaximalUnramifiedExtension l ∧ Module.finrank ℚ_[l] ↥E.1 = r ∧ (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c ↔ (c : Om l) ∈ E.1) ∧
    (∀ k, fr l r (ω k) = ω k) ∧ LinearIndependent ℚ_[l] ω ∧
    (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) ∧
    (Matrix.of fun m k : Fin r => fr l m (ω k)).det ≠ 0 := by
  intro l _ r hr
  let σ := sig l
  let F : IntermediateField ℚ_[l] ↥(MaximalUnramifiedExtension l) := IntermediateField.fixedField (Subgroup.zpowers (σ ^ r))
  have hF : ∀ c, c ∈ F ↔ fr l r c = c := fun c => by
    rw [IntermediateField.mem_fixedField_iff, ← sig_pow]
    refine ⟨fun h => h _ (Subgroup.mem_zpowers _), fun h f hf => ?_⟩
    exact (Subgroup.zpowers_le (H := MulAction.stabilizer _ c)).2 h hf
  have hst : ∀ c ∈ F, σ c ∈ F := fun c hc => by
    rw [hF, ← sig_pow] at hc ⊢
    rw [← AlgEquiv.mul_apply, ← pow_succ, pow_succ', AlgEquiv.mul_apply, hc]
  let τ₀ : ↥F →ₐ[ℚ_[l]] ↥F := ((σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)).comp F.val).codRestrict F.toSubalgebra
    fun c => hst c c.2
  let τ : ↥F ≃ₐ[ℚ_[l]] ↥F := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact AlgEquiv.ofBijective τ₀ (Algebra.IsAlgebraic.algHom_bijective _)
  have hτ : ∀ (k : ℕ) (c : ↥F), (((τ ^ k) c : ↥F) : ↥(MaximalUnramifiedExtension l)) = fr l k c := fun k c => by
    rw [← sig_pow]
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← ih]; rfl
  have hrτ : τ ^ r = 1 := AlgEquiv.ext fun c => Subtype.ext ((hτ r c).trans ((hF c).1 c.2))
  have hord : orderOf τ = r := by
    rw [orderOf_eq_iff hr]
    refine ⟨hrτ, fun k hkr hk0 hk => ?_⟩
    obtain ⟨c, hc, hm⟩ := exists_moved l hk0 hkr
    have := hτ k ⟨c, (hF c).2 hc⟩
    rw [hk, AlgEquiv.one_apply] at this
    exact hm this.symm
  have hfin : IsOfFinOrder τ := isOfFinOrder_iff_pow_eq_one.2 ⟨r, hr, hrτ⟩
  haveI : Finite ↥(Subgroup.zpowers τ) := hfin.finite_zpowers
  have hbot : IntermediateField.fixedField (Subgroup.zpowers τ) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [IntermediateField.mem_fixedField_iff] at hc
    have h1 := congrArg Subtype.val (hc τ (Subgroup.mem_zpowers _))
    have h2 := hτ 1 c
    rw [pow_one] at h2
    obtain ⟨x, hx⟩ := (GlobalTheory.MemLoc.frob_laws l (frobUr l) frobUr_root).2.2 c (h2.symm.trans h1)
    exact ⟨x, Subtype.ext hx⟩
  haveI h1 : FiniteDimensional ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) ↥F :=
    inferInstanceAs (FiniteDimensional ↥(FixedPoints.subfield (Subgroup.zpowers τ) ↥F) ↥F)
  haveI h2 : FiniteDimensional ℚ_[l] ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) := by
    rw [hbot]; infer_instance
  haveI h3 : FiniteDimensional ℚ_[l] ↥F := Module.Finite.trans ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) ↥F
  have hdeg : Module.finrank ℚ_[l] ↥F = r := by
    have h := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers τ)
    rw [hbot, IntermediateField.finrank_bot', Nat.card_zpowers] at h
    exact h.trans hord
  let bas : Module.Basis (Fin r) ℚ_[l] ↥F := Module.finBasisOfFinrankEq ℚ_[l] ↥F hdeg
  refine ⟨⟨F.map (MaximalUnramifiedExtension l).val, (F.equivMap (MaximalUnramifiedExtension l).val).toLinearEquiv.finiteDimensional⟩, fun k => (bas k : ↥(MaximalUnramifiedExtension l)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, -, rfl⟩
    exact y.2
  · show Module.finrank ℚ_[l] ↥(F.map (MaximalUnramifiedExtension l).val) = r
    rw [← (F.equivMap (MaximalUnramifiedExtension l).val).toLinearEquiv.finrank_eq]
    exact hdeg
  · intro c
    show _ ↔ (c : Om l) ∈ F.map (MaximalUnramifiedExtension l).val
    rw [IntermediateField.mem_map, ← hF]
    refine ⟨fun h => ⟨c, h, rfl⟩, ?_⟩
    rintro ⟨y, hy, hyc⟩
    rwa [← Subtype.ext hyc]
  · intro k
    exact (hF _).1 (bas k).2
  · exact bas.linearIndependent.map' F.val.toLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  · intro c hc
    refine ⟨bas.repr ⟨c, (hF c).2 hc⟩, ?_⟩
    have e := congrArg (F.val.toLinearMap) (bas.sum_repr ⟨c, (hF c).2 hc⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e
    simpa using e.symm
  · intro h0
    let M : Matrix (Fin r) (Fin r) ↥F := Matrix.of fun i j : Fin r => (τ ^ (j : ℕ)) (bas i)
    have e : (Matrix.of fun m k : Fin r => fr l m (bas k : ↥(MaximalUnramifiedExtension l))) = (F.val.mapMatrix M).transpose := by
      refine Matrix.ext fun m k => ?_
      simp only [M, Matrix.of_apply, Matrix.transpose_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
      exact (hτ m (bas k)).symm
    rw [e, Matrix.det_transpose, ← AlgHom.map_det] at h0
    exact det_pow_ne_zero τ hord bas (Subtype.ext h0)

end GlobalTheory.PMon.UnrDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachKernelMemFrobeniusSpanAfterQPow
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.PhiSpanKer

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem φD_smulA' (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  have h := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at h
  exact h

theorem map_smulA {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x := by
  rw [← algebraMap_smul W.EE a x, LinearMap.map_smul, algebraMap_smul]

variable {m : ℕ} (u : Fin m → LetA O n)

theorem mem_sum_form (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T))
    (hdec : ∀ a : LetA O n, ∃ c : Fin m → LetA O n, a = ∑ j, u j * W.φA (c j))
    {w : W.DD T} (hw : w ∈ φspan W T S) :
    ∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w = ∑ j, u j • W.φD T (z j) := by
  have hadd : ∀ w w' : W.DD T,
      (∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w = ∑ j, u j • W.φD T (z j)) →
      (∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w' = ∑ j, u j • W.φD T (z j)) →
      ∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w + w' = ∑ j, u j • W.φD T (z j) := by
    rintro w w' ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
    refine ⟨z + z', fun j => S.add_mem (hz j) (hz' j), ?_⟩
    simp only [Pi.add_apply, map_add (f := _), smul_add, Finset.sum_add_distrib]
  have key : ∀ w ∈ φspan W T S, ∀ a : LetA O n,
      ∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ a • w = ∑ j, u j • W.φD T (z j) := by
    intro w hw
    unfold φspan at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      intro a
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hdec a
      refine ⟨fun j => c j • y, fun j => S.smul_mem _ hy, ?_⟩
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [φD_smulA', mul_smul]
    | zero => intro a; exact ⟨0, fun j => S.zero_mem, by simp⟩
    | add x y _ _ hx hy => intro a; rw [smul_add]; exact hadd _ _ (hx a) (hy a)
    | smul b x _ hx => intro a; rw [smul_smul]; exact hx (a * b)
  simpa using key w hw 1

theorem phispan_of (hdec : ∀ a : LetA O n, ∃ c : Fin m → LetA O n, a = ∑ j, u j * W.φA (c j))
    {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L)
    (hinj : Function.Injective (W.map ι)) (hex : Function.Exact (W.map ι) (W.map π))
    (hπN : ∀ x ∈ W.N T₁, W.map π x ∈ W.N T₂)
    (hind : ∀ z : Fin m → W.DD T₂, (∀ j, z j ∈ W.N T₂) →
      ∑ j, u j • W.φD T₂ (z j) = 0 → ∀ j, z j = 0) :
    ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (LetA O n)),
      ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (LetA O n))) := by
  intro y hy
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply] at hy
  obtain ⟨k, hk⟩ := W.N_φinv T₁ _ hy
  refine ⟨k, ?_⟩
  have hk' : W.Q ^ k • W.map ι y ∈ φspan W T₁ (W.N T₁) := hk
  obtain ⟨w, hw, he⟩ := mem_sum_form W u T₁ (W.N T₁) hdec hk'
  have hπ0 : ∀ j, W.map π (w j) = 0 := by
    refine hind _ (fun j => hπN _ (hw j)) ?_
    have h1 := congrArg (W.map π) he
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smulA, (hex _).2 ⟨y, rfl⟩, smul_zero, map_sum] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulA, W.map_φ]
  choose w' hw' using fun j => (hex (w j)).1 (hπ0 j)
  have hmem : ∀ j, w' j ∈ (W.N T₁).comap ((W.map ι).restrictScalars (LetA O n)) := by
    intro j
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, hw']
    exact hw j
  have heq : W.Q ^ k • y = ∑ j, u j • W.φD T₀ (w' j) := by
    apply hinj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smulA, he, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulA, W.map_φ, hw']
  rw [heq]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w' j, hmem j, rfl⟩)

end Generic

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π c0 c1 c2 hses
  have hex : Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) := by
    let E := ((F l).E K s LL h).tie
    haveI := GlobalTheory.EtaleExact.finite_OL LL
    haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
    have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
    refine GlobalTheory.EtaleExact.exact_of_tie E (GlobalTheory.EtaleExact.map_ne_top_of_tie E ?_ ?_) T₀ T₁ T₂ ι π hses
    · rw [hp]
      exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow (D.loc l) LL
    · rw [hp]
      exact GlobalTheory.EtaleExact.sep_RW LL
  exact phispan_of W (fun j : Fin l => (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL))
    (GlobalTheory.T.wachLetterRing_frobenius_decomposition D HW l K s LL h) ι π hex.1 hex.2.1 (fun x hx => W.map_N π c1 c2 x hx)
    (GlobalTheory.T.wachFrobenius_flat_crystalline D HW F l K s LL h T₂ c2)

end GlobalTheory.NL.PhiSpanKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.JumpDR

theorem zA_eq_algebraMap_pt (l : ℕ) [Fact l.Prime] (z : ℤ_[l]) :
    Per.zA l z = algebraMap ℤ_[l] (Ainf l) z := by
  haveI : IsAdicComplete (Ideal.span {(l : WittVector l (PreTilt (OC l) l))}) (WittVector l (PreTilt (OC l) l)) :=
    WittVector.isAdicCompleteIdealSpanP
  have h := padicInt_ringHom_ext_of_isHausdorff l (WittVector l (PreTilt (OC l) l)) (Per.zA l) (algebraMap ℤ_[l] (Ainf l))
  exact RingHom.congr_fun h z

section Rings

variable {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)

def cB : Per.Bcris l →+* Pl.R.BdR :=
  (Pl.ιB : Pl.R.B →+* Pl.R.BdR).comp (Td.eB.symm : Per.Bcris l →+* Pl.R.B)

theorem cB_algebraMap (z : ℤ_[l]) :
    cB Td (algebraMap ℤ_[l] (Per.Bcris l) z) = algebraMap ℚ_[l] Pl.R.BdR (z : ℚ_[l]) := by
  have h : Td.eB.symm (Per.zB l z) = algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l]) := by
    rw [← Td.zB z, RingEquiv.symm_apply_apply]
  have hz : Per.zB l z = algebraMap ℤ_[l] (Per.Bcris l) z :=
    (GlobalTheory.RingIface.zB_eq_aB_zA l z).trans (congrArg (Per.aB l) (zA_eq_algebraMap_pt l z))
  rw [← hz]
  change Pl.ιB (Td.eB.symm (Per.zB l z)) = _
  rw [h, AlgHom.commutes]

def cD : Per.BdRp l →+* Pl.R.BdR :=
  (Td.eD.symm : Per.BdR l →+* Pl.R.BdR).comp (algebraMap (Per.BdRp l) (Per.BdR l))

theorem cD_algebraMap (z : ℤ_[l]) :
    cD Td (algebraMap ℤ_[l] (Per.BdRp l) z) = algebraMap ℚ_[l] Pl.R.BdR (z : ℚ_[l]) := by
  have h : Td.eD.symm (Per.zD l z) = algebraMap ℚ_[l] Pl.R.BdR (z : ℚ_[l]) := by
    rw [← Td.zD z, RingEquiv.symm_apply_apply]
  have hz : Per.zD l z = algebraMap (Per.BdRp l) (Per.BdR l) (algebraMap ℤ_[l] (Per.BdRp l) z) :=
    (GlobalTheory.RingIface.zD_eq_alg l z).trans (congrArg (fun x => algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l x))
      (zA_eq_algebraMap_pt l z))
  rw [hz] at h
  exact h

end Rings

section Hat

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]


variable (O) in
def kLift (c : ZMod a → AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : K))) : ZMod a → Ahat O K l e :=
  fun τ => AhatEq.equivAhat O K l e (PowerSeries.C (c τ))

def hsum (P : PhiMod O K l e a ι) {n : ℕ} (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → Vec K a ι) :
    ZMod a → ι → AhatE O K l e :=
  fun τ i => ∑ k, algebraMap (Ahat O K l e) (AhatE O K l e) (s k τ) * P.hatTot (m k) τ i


variable (O K l e) in
def InEhat (j : ℤ) (w : ZMod a → ι → AhatE O K l e) : Prop :=
  ∃ N : ℕ, 0 ≤ j + N ∧ ∀ τ i, ∃ x : Ahat O K l e,
    algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e ^ (j + N).toNat * x) =
      algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e ^ N) * w τ i

end Hat

end GlobalTheory.BKGal.JumpDR
end
end

