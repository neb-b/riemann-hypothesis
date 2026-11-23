module

public import Mathlib
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ZMemPerp

@[expose] public section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def UnimodOneGenus : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → h.Nondegenerate →
    ∀ L M : Submodule (𝓞 K) V, Submodule.IsLattice K L → Submodule.IsLattice K M →
      Formalism.HermitianLatticesTheory.IsUnimodular h L → Formalism.HermitianLatticesTheory.IsUnimodular h M → Formalism.HermitianLatticesTheory.SameGenus h L M

section Constr

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def aaI (a : Fin D.R.rS) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))

def PartnerOK (f : Fin D.R.rS → (VS D).V) : Prop :=
  (∀ a b, (VS D).hT (F0.e a) (f b) = if a = b then 1 else 0) ∧ (∀ a b, (VS D).hT (f a) (f b) = 0) ∧
    ∀ a, (VS D).hT (f a) F0.z = 0

def vPr (f : Fin D.R.rS → (VS D).V) (v : (VS D).V) : (VS D).V :=
  v - ∑ a, (VS D).hT (F0.e a) v • f a

theorem vPr_add (f : Fin D.R.rS → (VS D).V) (v w : (VS D).V) :
    vPr D F0 f (v + w) = vPr D F0 f v + vPr D F0 f w := by
  simp only [vPr, map_add (f := _), add_smul, Finset.sum_add_distrib]
  abel

theorem vPr_smul (f : Fin D.R.rS → (VS D).V) (c : D.host.E) (v : (VS D).V) :
    vPr D F0 f (c • v) = c • vPr D F0 f v := by
  simp only [vPr, map_smul, smul_eq_mul, mul_smul, smul_sub, Finset.smul_sum]

theorem vPr_zero (f : Fin D.R.rS → (VS D).V) : vPr D F0 f 0 = 0 := by
  simp [vPr]

theorem fi_add {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} {x y : D.host.E}
    (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by
  have h := Submodule.add_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    (FractionalIdeal.mem_coe.mpr hx) (FractionalIdeal.mem_coe.mpr hy)
  exact FractionalIdeal.mem_coe.mp h

theorem fi_zero (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : (0 : D.host.E) ∈ I := by
  exact FractionalIdeal.mem_coe.mp (Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E))

theorem fi_mul {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} (o : 𝓞 D.host.E) {x : D.host.E}
    (hx : x ∈ I) : (o : D.host.E) * x ∈ I := by
  have h := Submodule.smul_mem (I : Submodule (𝓞 D.host.E) D.host.E) o (FractionalIdeal.mem_coe.mpr hx)
  rw [Algebra.smul_def] at h
  exact FractionalIdeal.mem_coe.mp h

theorem star_int (o : 𝓞 D.host.E) : ∃ o' : 𝓞 D.host.E, (o' : D.host.E) = star (o : D.host.E) := by
  exact ⟨NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E) o, rfl⟩

def lamC (f : Fin D.R.rS → (VS D).V) (M : Submodule (𝓞 D.host.E) (WbQ D F0)) :
    Submodule (𝓞 D.host.E) (VS D).V where
  carrier := {v | (∀ a, star ((VS D).hT (F0.e a) v) ∈ (aaI D a)⁻¹) ∧
    (∃ w : perpS (VS D) F0.X, (w : (VS D).V) = vPr D F0 f v ∧ (Submodule.Quotient.mk w : WbQ D F0) ∈ M) ∧
    ∀ a, (VS D).hT (f a) (vPr D F0 f v) ∈ aaI D a}
  add_mem' := by
    rintro v v' ⟨h1, ⟨w, hw, hwM⟩, h3⟩ ⟨h1', ⟨w', hw', hwM'⟩, h3'⟩
    refine ⟨fun a => ?_, ⟨w + w', ?_, ?_⟩, fun a => ?_⟩
    · rw [map_add (f := _), star_add]; exact fi_add D (h1 a) (h1' a)
    · rw [Submodule.coe_add, hw, hw', vPr_add]
    · rw [Submodule.Quotient.mk_add]; exact M.add_mem hwM hwM'
    · rw [vPr_add, map_add (f := _)]; exact fi_add D (h3 a) (h3' a)
  zero_mem' := by
    refine ⟨fun a => ?_, ⟨0, ?_, ?_⟩, fun a => ?_⟩
    · simp only [map_zero, star_zero]; exact fi_zero D _
    · simp [vPr_zero]
    · simp
    · simp only [vPr_zero, map_zero]; exact fi_zero D _
  smul_mem' := by
    rintro o v ⟨h1, ⟨w, hw, hwM⟩, h3⟩
    have hs : o • v = (o : D.host.E) • v := (algebraMap_smul D.host.E o v).symm
    refine ⟨fun a => ?_, ⟨o • w, ?_, ?_⟩, fun a => ?_⟩
    · obtain ⟨o', ho'⟩ := star_int D o
      rw [hs, map_smul, smul_eq_mul, star_mul, ← ho', mul_comm]
      exact fi_mul D o' (h1 a)
    · rw [hs, vPr_smul, ← hw]
      show o • (w : (VS D).V) = _
      exact (algebraMap_smul D.host.E o (w : (VS D).V)).symm
    · rw [Submodule.Quotient.mk_smul]; exact M.smul_mem o hwM
    · rw [hs, vPr_smul, map_smul, smul_eq_mul]; exact fi_mul D o (h3 a)

end Constr

def PartnerEx : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)), ∃ f, PartnerOK D F0 f

def LamLattice : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (f : Fin D.R.rS → (VS D).V)
    (M : Submodule (𝓞 D.host.E) (WbQ D F0)), PartnerOK D F0 f → IsGlueLat (hWb D F0) (zbar D F0) M →
      Submodule.IsLattice D.host.E (lamC D F0 f M)

def LamUnimod : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (f : Fin D.R.rS → (VS D).V)
    (M : Submodule (𝓞 D.host.E) (WbQ D F0)), PartnerOK D F0 f → IsGlueLat (hWb D F0) (zbar D F0) M →
      Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (lamC D F0 f M)

def LamFlag : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (f : Fin D.R.rS → (VS D).V)
    (M : Submodule (𝓞 D.host.E) (WbQ D F0)), PartnerOK D F0 f → IsGlueLat (hWb D F0) (zbar D F0) M →
      F0.z ∈ lamC D F0 f M ∧ XLam (lamC D F0 f M) (lf D F0) = XS D F0 ∧
      (∀ c : D.host.E, c • F0.z ∈ Lsub (lamC D F0 f M) (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) ∧
      Mof D F0 (lamC D F0 f M) = M

def LocGenXS : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ∃ c : Fin D.R.rS → D.host.E, (∀ a, c a ≠ 0) ∧
      (((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ a, c a = 1) ∧
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XS D F0) =
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a)))

private theorem row_riesz (D : Formalism.BasicNotions.D7) (φ : (VS D).V →ₗ[D.host.E] D.host.E) : ∃ μ : (VS D).V, ∀ v, (VS D).hT μ v = φ v := by
  classical
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis (VS D).hT (VS D).nondeg (VS D).frame
  refine ⟨∑ j, star (φ ((VS D).frame j)) • bs j, fun v => ?_⟩
  have key : (VS D).hT (∑ j, star (φ ((VS D).frame j)) • bs j) = φ := by
    apply (VS D).frame.ext
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    have hs : ∀ j, (VS D).hT (star (φ ((VS D).frame j)) • bs j) ((VS D).frame i) =
        φ ((VS D).frame j) * (if i = j then 1 else 0) := by
      intro j
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
      congr 1
      rw [← (VS D).herm.eq ((VS D).frame i) (bs j), hbs]
      split_ifs <;> simp
    simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [key]

private theorem row_span_eq_top_of_unimodular (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hL : Λ.FG) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) :
    Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ := by
  by_contra hspan
  obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨μ, hμ⟩ := row_riesz D φ
  have hμ₀ : μ ≠ 0 := by
    intro h
    apply hφ₀
    ext y
    simpa [h] using (hμ y).symm
  have hline (a : D.host.E) : a • μ ∈ Λ := by
    rw [← hU]
    change a • μ ∈ Formalism.E.hdual (VS D).hT Λ
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    intro y hy
    have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
    simp [← (VS D).herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
  obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
    (show μ ∉ (⊥ : Submodule D.host.E (VS D).V) by simpa using hμ₀)
  let f := ψ.restrictScalars (𝓞 D.host.E)
  have hmap (x : D.host.E) : x ∈ Λ.map f := by
    refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
    change ψ ((x / ψ μ) • μ) = x
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
  obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
    (S := nonZeroDivisors (𝓞 D.host.E)) (hL.map f)
  have hinj := IsFractionRing.injective (𝓞 D.host.E) D.host.E
  have hne {a : 𝓞 D.host.E} (ha : a ≠ 0) : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 :=
    fun h => ha (hinj (h.trans (map_zero _).symm))
  have hinteger (x : D.host.E) : IsLocalization.IsInteger (𝓞 D.host.E) x := by
    have hx := hd _ (hmap ((algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ * x))
    rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
      one_mul] at hx
  apply RingOfIntegers.not_isField D.host.E
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 D.host.E) D.host.E a)⁻¹)
  refine ⟨b, hinj ?_⟩
  rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]


theorem rowSurj_of (hJ : UnimodOneGenus) (hP : PartnerEx) (hL : LamLattice) (hU : LamUnimod)
    (hF : LamFlag) (hG : LocGenXS) : RowSurj := by
  intro D u F0 M hM
  obtain ⟨f, hf⟩ := hP D u F0
  obtain ⟨hz, hX, hprim, hMof⟩ := hF D u F0 f M hf hM
  have hLat := hL D u F0 f M hf hM
  have hUn := hU D u F0 f M hf hM
  have hFull : Submodule.IsFullLattice D.host.E (lamC D F0 f M) :=
    { toIsLattice := hLat, span_eq_top := row_span_eq_top_of_unimodular D hLat.fg hUn }
  refine ⟨lamC D F0 f M, ?_, hMof⟩
  refine ⟨?_, ⟨hLat, hUn, ⟨hz, rfl⟩, ?_, hprim⟩, hX⟩
  ·
    exact ⟨hFull, hJ D.host.E (VS D).V (VS D).hT D.sp.cm.cmUnram (VS D).herm (VS D).nondeg
      (VS D).L0 (lamC D F0 f M) (VS D).standardTuple_isLattice hLat (VS D).baseLattice_isUnimodular hUn⟩
  · intro P
    rw [hX]
    exact hG D u F0 P

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
