module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensCntRes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0007

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BasIntSmulMem
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

section Bas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem basRatV_add (x y : Fin n → E) :
    ratV (F := F) (Fv F v) (x + y) = ratV (F := F) (Fv F v) x + ratV (F := F) (Fv F v) y := by
  funext i
  simp [ratV, map_add (f := _)]

theorem basRatV_zsmul (c : ℤ) (x : Fin n → E) :
    ratV (F := F) (Fv F v) (c • x) = c • ratV (F := F) (Fv F v) x := by
  funext i
  simp [ratV]

theorem basRatV_zero : ratV (F := F) (Fv F v) (0 : Fin n → E) = 0 := by
  funext i
  simp [ratV]

theorem basRatV_single (i : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (Pi.single i e : Fin n → E) =
      (Pi.single i (inclR (F := F) (Fv F v) e) : Fin n → Fv F v ⊗[F] E) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [ratV]
  · simp [ratV, Pi.single_eq_of_ne h]

theorem basInt_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ y • x ∈ L := by
  classical
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  obtain ⟨m, f, g, rfl⟩ := Submodule.mem_span_set'.1 hx
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ (y • f i) := hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  convert L.smul_mem (⟨y • f i, hi⟩ : 𝓞 E) (g i).2 using 1
  rw [← smul_assoc]
  rfl

theorem basLat_fg (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsLattice E L) :
    (latLoc (E := E) v (L : Set (Fin n → E))).FG := by
  classical
  obtain ⟨s, hs⟩ : (L.restrictScalars ℤ).FG := hLat.fg.restrictScalars
  refine ⟨s.image (ratV (F := F) (Fv F v)), ?_⟩
  rw [Finset.coe_image]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hxL : x ∈ L := by
      have : x ∈ L.restrictScalars ℤ := by
        rw [← hs]
        exact Submodule.subset_span hx
      exact this
    exact Submodule.subset_span ⟨x, hxL, rfl⟩
  · unfold latLoc
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Submodule.span ℤ (s : Set (Fin n → E)) := by
      rw [hs]
      exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      rw [basRatV_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [basRatV_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [basRatV_zsmul]
      exact zsmul_mem hy c

theorem basSpan_top (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsFullLattice E L) :
    Submodule.span (Fv F v) (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) = ⊤ := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let bE := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (Fv F v) bE
  let P := Pi.basis (fun _ : Fin n => B)
  rw [eq_top_iff, ← P.span_eq, Submodule.span_le]
  rintro _ ⟨⟨i, k⟩, rfl⟩
  obtain ⟨N, hN, hNL⟩ := basInt_smul_mem L hLat.span_eq_top (Pi.single i (bE k) : Fin n → E)
  have hN' : (N : Fv F v) ≠ 0 := by
    rw [← map_intCast (algebraMap F (Fv F v))]
    exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hN)
  have hmem : ratV (F := F) (Fv F v) (N • (Pi.single i (bE k) : Fin n → E)) ∈
      latLoc (E := E) v (L : Set (Fin n → E)) := Submodule.subset_span ⟨_, hNL, rfl⟩
  have e : P ⟨i, k⟩ = (N : Fv F v)⁻¹ • ratV (F := F) (Fv F v) (N • (Pi.single i (bE k) : Fin n → E)) := by
    rw [basRatV_zsmul, basRatV_single, ← Int.cast_smul_eq_zsmul (Fv F v), smul_smul, inv_mul_cancel₀ hN', one_smul]
    simp only [P, B, Pi.basis_apply, Algebra.TensorProduct.basis_apply]
    rfl
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end Bas

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.GramCoord
section
noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem phi_surj (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e)
    (he1 : gramR (Fv F v) σ J e = 1) {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K}
    {π : OR (E := E) v →+* K} (hπ : IsRes σ v ϖ τ π) (a : ℕ) :
    Function.Surjective (phi σ J v Λ hSD he π a) := by
  intro M
  choose c hc using fun i p => hπ.1 (M i p)
  have hX : (fun i => ∑ p, (c i p : Fv F v ⊗[F] E) • e p) ∈ lamA v Λ a := fun i =>
    (he _).2 ⟨fun p => (c i p : Fv F v ⊗[F] E), fun p => (c i p).2, rfl⟩
  refine ⟨⟨_, hX⟩, ?_⟩
  funext i p
  rw [phi_apply]
  have h : cf σ J v Λ hSD he ⟨_, hX⟩ i p = c i p := by
    apply Subtype.ext
    rw [cf_coe]
    exact coord_eq σ J v e he1 (fun q => (c i q : Fv F v ⊗[F] E)) p
  rw [h, hc]

theorem phi_ker (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e)
    (he1 : gramR (Fv F v) σ J e = 1) {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K}
    {π : OR (E := E) v →+* K} (hπ : IsRes σ v ϖ τ π) (a : ℕ) :
    (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a) = (phi σ J v Λ hSD he π a).ker := by
  ext X
  rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨Z, hZ, hZX⟩
    funext i p
    rw [phi_apply, Pi.zero_apply, Pi.zero_apply]
    apply (hπ.2.1 _).2
    rw [cf_coe, ← hZX]
    refine ⟨hR (Fv F v) σ J (e p) (Z i), (hSD _).1 (hZ i) _ (bas_mem v Λ he p), ?_⟩
    show hR (Fv F v) σ J (e p) (sc (E := E) v ϖ • Z i) = _
    rw [Orb.hR_smul_right]
  · intro h0
    have hP : ∀ i p, ∃ d ∈ OEv (E := E) v,
        hR (Fv F v) σ J (e p) ((X : TupV (E := E) v n a) i) = sc (E := E) v ϖ * d := by
      intro i p
      have := (hπ.2.1 (cf σ J v Λ hSD he X i p)).1 (by
        have h1 := congrFun (congrFun h0 i) p
        rw [phi_apply] at h1
        exact h1)
      exact this
    choose d hd hde using hP
    have hZ : (fun i => ∑ p, d i p • e p) ∈ lamA v Λ a := fun i => (he _).2 ⟨d i, hd i, rfl⟩
    refine ⟨_, hZ, ?_⟩
    funext i
    rw [DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, expand σ J v Λ he he1 (memA v Λ X i), Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hde, smul_smul]

theorem gram_coord (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (hSD : IsSDLoc σ J v Λ)
    {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1) {a : ℕ}
    (X : lamA v Λ a) (i j : Fin a) :
    gramR (Fv F v) σ J (X : TupV (E := E) v n a) i j = ∑ p, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (cf σ J v Λ hSD he X i p : Fv F v ⊗[F] E) *
      (cf σ J v Λ hSD he X j p : Fv F v ⊗[F] E) := by
  show hR (Fv F v) σ J ((X : TupV (E := E) v n a) i) ((X : TupV (E := E) v n a) j) = _
  conv_lhs => rw [expand σ J v Λ he he1 (memA v Λ X j)]
  rw [Orb.hR_sum_right σ J v]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [cf_coe, cf_coe, Orb.hR_conj σ J v hcm hJ, mul_comm]

end PI.OmLocU.Red
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MeasUOfBas
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem lamT_open (a : ℕ) (Y : TupV (E := E) v n a) (hB : LatBasO σ J ψ v Λ a Y) (hG : GoodY σ J ψ v Λ a Y) :
    IsOpen (LamT v Λ a) := by
  obtain ⟨b, hb, hmem⟩ := hB hG
  have hCM := hG.1.1
  have hfr : Module.finrank F E = 2 := hCM.2.2.1
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hfr]; norm_num)
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hV : Module.finrank (Fv F v) (Fin n → Fv F v ⊗[F] E) = 2 * n := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Module.finrank_baseChange, hfr, mul_comm]
  have : FiniteDimensional (Fv F v) (Fin n → Fv F v ⊗[F] E) := inferInstance
  let bb := basisOfLinearIndependentOfCardEqFinrank' b hb (by rw [Fintype.card_fin, hV])
  have hbb : ∀ i, bb i = b i := fun i => by simp [bb]
  have e : (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) =
      bb.equivFun.symm '' Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x
    constructor
    · intro hx
      obtain ⟨c, rfl⟩ := (hmem x).1 hx
      refine ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, ?_⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hbb]
    · rintro ⟨c, hc, rfl⟩
      refine (hmem _).2 ⟨fun i => ⟨c i, hc i (Set.mem_univ i)⟩, ?_⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hbb]
  have hc : Continuous bb.equivFun := IsModuleTopology.continuous_of_linearMap bb.equivFun.toLinearMap
  have hL : IsOpen (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
    rw [e, LinearEquiv.image_eq_preimage_symm, LinearEquiv.symm_symm]
    exact (isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _).preimage hc
  have : LamT v Λ a = Set.univ.pi (fun _ => (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))) := by
    ext X
    simp [LamT]
  rw [this]
  exact isOpen_set_pi Set.finite_univ fun _ _ => hL

theorem measU_of_bas (a : ℕ) (Y : TupV (E := E) v n a) (hB : LatBasO σ J ψ v Λ a Y) :
    MeasU σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have := PI.VolStabSW.secondCountable_Fv F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hOpen := lamT_open σ J ψ v Λ a Y hB hG
  refine ⟨inferInstance, hOpen.measurableSet, ?_⟩
  have e : (lamP v Λ a ϖ : Set (TupV (E := E) v n a)) = (fun X => ϖ • X) '' LamT v Λ a := by
    unfold lamP
    rw [AddSubgroup.coe_map]
    congr 1
    funext X
    funext i p
    show sc (E := E) v ϖ * X i p = ϖ • X i p
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [e]
  exact (isOpenMap_smul₀ (unif_ne_zero v hϖ) _ hOpen).measurableSet

theorem countU_of_bas' (a : ℕ) (Y : TupV (E := E) v n a)
    (hB : LatBasO σ J ψ v Λ a Y) (hQ : ResIdx v) (hR : RedU σ J ψ v Λ a Y) : CountU σ J ψ v Λ a Y :=
  countU_of σ J ψ v Λ a Y (measU_of_bas σ J ψ v Λ a Y hB)
    (idxU_of σ J ψ v Λ a Y (idxV_of σ J ψ v Λ a Y hB hQ)) (clsU_of σ J ψ v Λ a Y hR)

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUnifOIff
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.VolStabSW

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem le_ofAdd_neg_one_of_lt_one_local_unitary_orbits {a : WithZero (Multiplicative ℤ)} (h : a < 1) :
    a ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  by_cases ha : a = 0
  · simp [ha]
  · have h1 : a < ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      simpa using h
    rw [WithZero.lt_ofAdd_iff ha] at h1
    rw [WithZero.le_ofAdd_iff ha]
    omega

theorem mem_unifO_iff {ϖ : Fv F v} (hϖ : IsUnif v ϖ) (x : v.adicCompletionIntegers F) :
    x ∈ unifO v ϖ ↔ Valued.v (x : Fv F v) < 1 := by
  have hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := hϖ
  have hlt : Valued.v ϖ < 1 := by
    rw [hv]
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1)
  have hne : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact WithZero.zero_ne_coe hv
  constructor
  · rintro ⟨d, hd⟩
    have hd1 : Valued.v (d : Fv F v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 d.2
    rw [hd, map_mul]
    calc Valued.v ϖ * Valued.v (d : Fv F v) ≤ Valued.v ϖ * 1 := by gcongr
      _ < 1 := by rwa [mul_one]
  · intro hx
    have hle : Valued.v (x : Fv F v) ≤ Valued.v ϖ := by
      rw [hv]; exact le_ofAdd_neg_one_of_lt_one_local_unitary_orbits hx
    have hmem : (x : Fv F v) / ϖ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
      exact div_le_one_of_le₀ hle zero_le'
    refine ⟨⟨_, hmem⟩, ?_⟩
    simp only
    field_simp

def redO : v.adicCompletionIntegers F →+ 𝓞 F ⧸ v.asIdeal where
  toFun x := red v (x : Fv F v)
  map_zero' := red_zero v
  map_add' x y := red_add v x.2 y.2

theorem resIdx_holds : ResIdx v := by
  intro ϖ hϖ
  have hker : unifO v ϖ = (redO v).ker := by
    ext x
    rw [mem_unifO_iff v hϖ x, AddMonoidHom.mem_ker]
    exact (red_eq_zero_iff v x.2).symm
  have hsurj : Function.Surjective (redO v) := by
    intro t
    obtain ⟨y, hy, hyt⟩ := red_surj v t
    exact ⟨⟨y, hy⟩, hyt⟩
  rw [hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  simp

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SdVolHOfPi
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem sdVolW_of (a : ℕ) (hC : CondV σ J ψ v) (hD : DualW σ J ψ v Λ a) (hI : IdxW v Λ a)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    SdVolW σ J ψ v Λ a :=
  sdVolW_of_top σ J ψ v Λ a hC (topW_holds v Λ a hFull) hD hI

theorem sdVolH_of (a : ℕ) (hC : CondV σ J ψ v) (hD : DualH σ J ψ v a) (hI : IdxHO σ v a) :
    SdVolH σ J ψ v a :=
  sdVolH_of_top σ J ψ v a hC (topH_holds v σ a) hD hI

theorem sdVolW_of_pi (a : ℕ) (hC : CondV σ J ψ v) (hD : DualW σ J ψ v Λ a) (hI : IdxPiW v Λ a)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    SdVolW σ J ψ v Λ a :=
  sdVolW_of σ J ψ v Λ a hC hD (idxW_of v Λ a hI) hFull

theorem sdVolH_of_pi (a : ℕ) (hC : CondV σ J ψ v) (hD : DualH σ J ψ v a) (hI : IdxPiH σ v a) :
    SdVolH σ J ψ v a :=
  sdVolH_of σ J ψ v a hC hD (idxHO_of σ v a hI)

end PI.OmLocU
end
end

