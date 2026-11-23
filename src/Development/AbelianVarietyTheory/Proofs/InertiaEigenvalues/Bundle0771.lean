module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ReducedBasisStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompRestrictToHalfLatticeIndicator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.ExportSeries

namespace RestrictHalfModel

variable {D : D7} {m n : ℕ}

theorem isHalf_iff' (e : AE D) (u : Mx D m n) : IsHalf e u ↔ e • u = u := GlobalTheory.SplitScalar.isHalf_iff e u

theorem isHalf_smul {e : AE D} (he : e * e = e) (u : Mx D m n) : IsHalf e (e • u) := by
  rw [isHalf_iff', smul_smul, he]

theorem halfInd_smul_congr {e : AE D} (he : e * e = e) (Λ : AddSubgroup (Mx D m n)) {z t : Mx D m n}
    (h : e • z - e • t ∈ Λ) : halfInd e Λ (e • z) = halfInd e Λ (e • t) := by
  unfold halfInd
  have hz := isHalf_smul he z
  have ht := isHalf_smul he t
  by_cases h1 : e • t ∈ Λ
  · rw [if_pos ⟨by simpa using Λ.add_mem h h1, hz⟩, if_pos ⟨h1, ht⟩]
  · rw [if_neg fun h2 => h1 (by simpa using Λ.sub_mem h2.1 h), if_neg fun h2 => h1 h2.1]

theorem smul_of_half {a' b : AE D} (hab : a' * b = 0) {x : Mx D m n} (hx : IsHalf a' x) :
    b • x = 0 ∧ (a' + b) • x = x := by
  rw [isHalf_iff'] at hx
  have h0 : b • x = 0 := by
    rw [← hx, smul_smul, mul_comm, hab, zero_smul]
  exact ⟨h0, by rw [add_smul, hx, h0, add_zero]⟩

theorem isHalf_add_iff {e : AE D} {t u : Mx D m n} (hu : e • u = u) : IsHalf e (t + u) ↔ IsHalf e t := by
  rw [isHalf_iff', isHalf_iff', smul_add, hu, add_left_inj]

theorem isSBHalf_restrictHalf {a' b : AE D} (ha' : a' * a' = a') (hb : b * b = b) {Λ : AddSubgroup (Mx D m n)}
    (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Φ : Mx D m n → ℂ} (hΦ : IsSBHalf a' Λ Φ) :
    IsSBHalf (a' + b) Λ (restrictHalf a' b Λ Φ) := by
  obtain ⟨-, k, hk, hinv, hlat⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun u hu hhu t => ?_, fun t ht => ?_⟩
  · rw [restrictHalf_apply] at ht
    by_contra h
    exact ht (by rw [if_neg h, mul_zero])
  · rw [isHalf_iff'] at hhu
    simp only [restrictHalf_apply]
    have e1 : a' • (t + k • u) = a' • t + k • (a' • u) := by rw [smul_add, smul_comm]
    have e2 : (a' + b) • (k • u) = k • u := by rw [smul_comm, hhu]
    rw [e1, hinv _ (hΛ a' ha' u hu) (isHalf_smul ha' u), halfInd_smul_congr hb Λ (z := t + k • u) (t := t) (by
      rw [smul_add, add_sub_cancel_left, smul_comm]
      exact Λ.nsmul_mem (hΛ b hb u hu) k)]
    simp only [isHalf_add_iff e2]
  · rw [restrictHalf_apply] at ht
    have h1 : Φ (a' • t) ≠ 0 := fun h => ht (by rw [h, zero_mul, zero_mul])
    have h2 : halfInd b Λ (b • t) ≠ 0 := fun h => ht (by rw [h, mul_zero, zero_mul])
    have h3 : IsHalf (a' + b) t := by
      by_contra h
      exact ht (by rw [if_neg h, mul_zero])
    have h2' : b • t ∈ Λ := by
      unfold halfInd at h2
      by_contra h
      exact h2 (if_neg fun h' => h h'.1)
    rw [isHalf_iff', add_smul] at h3
    rw [← h3, smul_add]
    exact Λ.add_mem (hlat _ h1) (Λ.nsmul_mem h2' k)

end RestrictHalfModel


open RestrictHalfModel in
theorem isPlaceModel_comp_restrictHalf : ∀ {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ} {a' b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}, a' * a' = a' → b * b = b → a' * b = 0 → (∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a' + b) Λ 1 f₀ T₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a' Λ 1 f₀ (T₀ ∘ₗ restrictHalf a' b Λ) := by
  intro D S T ψ Λ f₀ a' b T₀ ha' hb hab hΛ hT
  have hsb : ∀ Φ, IsSBHalf a' Λ Φ → IsSBHalf (a' + b) Λ (restrictHalf a' b Λ Φ) :=
    fun Φ hΦ => isSBHalf_restrictHalf ha' hb hΛ hΦ
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · obtain ⟨hbx, hax⟩ := smul_of_half hab hx
    have hxa : IsHalf (a' + b) x := (isHalf_iff' _ _).2 hax
    have e : restrictHalf a' b Λ (fun t => Φ (t + x)) = fun t => restrictHalf a' b Λ Φ (t + x) := by
      funext z
      simp only [restrictHalf_apply]
      rw [smul_add, (isHalf_iff' _ _).1 hx, smul_add b, hbx, add_zero, isHalf_add_iff hax]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.trans _ (hsb Φ hΦ) x hxa
  · have hy' : IsHalf (cA D (a' + b)) y := by
      rw [isHalf_iff'] at hy ⊢
      rw [map_add (f := _), add_smul, hy, ← hy, smul_smul, ← map_mul, mul_comm, hab, map_zero, zero_smul, add_zero]
    have e : restrictHalf a' b Λ (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO S T t y) * restrictHalf a' b Λ Φ t := by
      funext z
      simp only [restrictHalf_apply]
      rw [GlobalTheory.SplitScalar.symplO_smul, (isHalf_iff' _ _).1 hy]
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.modul _ (hsb Φ hΦ) y hy'
  · have e : restrictHalf a' b Λ ((1 : ℂ) • halfInd a' Λ) = (1 : ℂ) • halfInd (a' + b) Λ := by
      funext t
      simp only [one_smul, restrictHalf_apply]
      unfold halfInd
      have i1 := isHalf_smul ha' t
      have i2 := isHalf_smul hb t
      by_cases hat : IsHalf (a' + b) t
      · have ht' : t = a' • t + b • t := by rw [← add_smul]; exact ((isHalf_iff' _ _).1 hat).symm
        by_cases ht : t ∈ Λ
        · rw [if_pos ⟨hΛ a' ha' t ht, i1⟩, if_pos ⟨hΛ b hb t ht, i2⟩, if_pos hat, if_pos ⟨ht, hat⟩]
          ring
        · rw [if_neg (show ¬ (t ∈ Λ ∧ IsHalf (a' + b) t) from fun h => ht h.1), if_pos hat, mul_one]
          by_cases h1 : a' • t ∈ Λ
          · rw [if_neg (show ¬ (b • t ∈ Λ ∧ IsHalf b (b • t)) from fun h => ht (by rw [ht']; exact Λ.add_mem h1 h.1)),
              mul_zero]
          · rw [if_neg (show ¬ (a' • t ∈ Λ ∧ IsHalf a' (a' • t)) from fun h => h1 h.1), zero_mul]
      · rw [if_neg hat, mul_zero, if_neg fun h => hat h.2]
    rw [LinearMap.comp_apply, e]
    exact hT.vac

end GlobalTheory.ExportSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTorsionFreeIntOf
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ConstBound

theorem isTorsionFree_int_of {E : Type} [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.IsTorsionFree (𝓞 E) X] : Module.IsTorsionFree ℤ X :=
  Module.IsTorsionFree.trans_faithfulSMul ℤ (𝓞 E) X

theorem datum_free {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (Dw : Datum H) :
    Module.Free ℤ Dw.La ∧ Module.Finite ℤ Dw.La := by
  have := Dw.fin
  have := Dw.proj
  have : Module.IsTorsionFree ℤ Dw.La := isTorsionFree_int_of (E := E) Dw.La
  have : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
  exact ⟨inferInstance, inferInstance⟩

theorem card_levQ_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (Dw : Datum H)
    (l : Geo.Tor.Level H) : Nat.card (LevQ Dw l) ∣ l.M ^ Module.finrank ℤ Dw.La := by
  obtain ⟨hfree, hfin⟩ := datum_free Dw
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at h1
    exact (Ideal.mul_le_inf.trans inf_le_left) h1
  have hle : (nsmulAddMonoidHom (α := Dw.La) l.M).range ≤ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).toAddSubgroup := by
    rintro x ⟨y, rfl⟩
    simp only [nsmulAddMonoidHom_apply, Submodule.mem_toAddSubgroup]
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hM Submodule.mem_top
  have key := AddSubgroup.index_dvd_of_le hle
  rw [AddSubgroup.index_range_nsmul] at key
  unfold LevQ
  exact key

private theorem relIndex_span_smul_stdLat {E : Type} [Field E] [NumberField E] {n : ℕ} (N : ℕ) :
    (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup.relIndex
      (Formalism.L2.Pj.stdLat E n).toAddSubgroup = N ^ (Module.finrank ℚ E * n) := by
  have hmem : ∀ v : Fin n → E, v ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, ∃ a : 𝓞 E, (a : E) = v i := by
    intro v
    simp only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  set L := (Formalism.L2.Pj.stdLat E n).toAddSubgroup with hL
  have hmap : (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup =
      L.map (nsmulAddMonoidHom N) := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, nsmulAddMonoidHom_apply,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists, hL]
    simp only [Nat.cast_smul_eq_nsmul]
  let g : (Fin n → 𝓞 E) →+ L :=
    { toFun := fun a => ⟨fun i => (a i : E), (hmem _).2 fun i => ⟨a i, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      funext i
      have := congrArg (fun v : L => (v : Fin n → E) i) hab
      exact RingOfIntegers.coe_injective this
    · rintro ⟨v, hv⟩
      choose a ha using (hmem v).1 hv
      exact ⟨a, Subtype.ext (funext ha)⟩
  let e : (Fin n → 𝓞 E) ≃ₗ[ℤ] L := (AddEquiv.ofBijective g hg).toIntLinearEquiv
  have : Module.Free ℤ L := Module.Free.of_equiv e
  have : Module.Finite ℤ L := Module.Finite.equiv e
  have hrank : Module.finrank ℤ L = Module.finrank ℚ E * n := by
    rw [← e.finrank_eq, Module.finrank_pi_fintype]
    simp [NumberField.RingOfIntegers.rank, mul_comm]
  rw [hmap, AddSubgroup.relIndex, AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range,
    AddSubgroup.index_range_nsmul, hrank]

theorem relIndex_dvd {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) (N : ℕ) (hN : 0 < N)
    (h : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ.Ln) :
    (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ∣ N ^ (Module.finrank ℚ E * n) := by
  have hHK : (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup ≤ Λ.Ln.toAddSubgroup :=
    fun x hx => h hx
  have hKL : Λ.Ln.toAddSubgroup ≤ (Formalism.L2.Pj.stdLat E n).toAddSubgroup :=
    fun x hx => (inf_le_right : Λ.La ⊓ Formalism.L2.Pj.stdLat E n ≤ _) hx
  rw [← relIndex_span_smul_stdLat N]
  exact Dvd.intro _ (AddSubgroup.relIndex_mul_relIndex _ _ _ hHK hKL)

theorem mIdx_dvd {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) (N r : ℕ) (hN : 0 < N)
    (h : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ.Ln) : Λ.mIdx N r ∣ N ^ (Module.finrank ℚ E * n * r) := by
  have key := relIndex_dvd Λ N hN h
  rw [AddSubgroup.relIndex] at key
  rw [Formalism.L2.Pj.GenLat.mIdx, pow_mul]
  exact pow_dvd_pow_of_dvd key r

theorem const_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (n d M p : ℕ), p.Prime → M ≠ 0 → ∃ c : ℕ, ∀ (l₂ : Geo.Tor.Level H) (pd u : ℕ) (Λ : GenLat E n), l₂.M = M * pd → ¬ p ∣ pd → Nat.Coprime u p → Λ.LevOK (l₂.M * u) l₂.M → ∃ u' : ℕ, Nat.Coprime u' p ∧ ((Λ.mIdx (l₂.M * u) (Dw.p + Dw.q) * Nat.card (Fin n → LevQ Dw l₂) : ℕ) : ℤ) * (2 * NumberField.discr E * (l₂.M * u : ℕ)) ^ d ∣ ((p ^ c * u' : ℕ) : ℤ) := by
  intro E _ _ _ H Dw n d M p hp hM
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hdisc : NumberField.discr E ≠ 0 := NumberField.discr_ne_zero E
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = (M : ℤ) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) *
      (M : ℤ) ^ (Module.finrank ℤ Dw.La * n) * (2 * NumberField.discr E * M) ^ d := ⟨_, rfl⟩
  have hK0 : K.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero, hK]
    have hM' : (M : ℤ) ≠ 0 := by exact_mod_cast hM
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hM') (pow_ne_zero _ hM'))
      (pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero hdisc) hM'))
  obtain ⟨c, k, hk, hKk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hK0 p hp1
  refine ⟨c, ?_⟩
  intro l₂ pd u Λ hl hpd hu hΛ
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hp1 (Nat.coprime_zero_left p |>.mp hu)
  have hN : 0 < l₂.M * u := Nat.mul_pos (by have := l₂.three_le; omega) (Nat.pos_of_ne_zero hu0)
  have h1 : Λ.mIdx (l₂.M * u) (Dw.p + Dw.q) ∣ (l₂.M * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) :=
    mIdx_dvd Λ _ _ hN hΛ.2.2
  have h2 : Nat.card (Fin n → LevQ Dw l₂) ∣ l₂.M ^ (Module.finrank ℤ Dw.La * n) := by
    rw [Nat.card_fun, Nat.card_fin, pow_mul]
    exact pow_dvd_pow_of_dvd (card_levQ_dvd Dw l₂) n
  have hcop : ∀ m : ℕ, ¬ p ∣ m → Nat.Coprime m p := fun m hm =>
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  have hpd' := hcop pd hpd
  refine ⟨k * ((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) *
    (pd * u) ^ d), ?_, ?_⟩
  · exact Nat.Coprime.mul_left (hcop k hk) (Nat.Coprime.mul_left (Nat.Coprime.mul_left
      (Nat.Coprime.pow_left _ (Nat.Coprime.mul_left hpd' hu)) (Nat.Coprime.pow_left _ hpd'))
      (Nat.Coprime.pow_left _ (Nat.Coprime.mul_left hpd' hu)))
  · have hKd : K ∣ (K.natAbs : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
    have h12 := Int.natCast_dvd_natCast.mpr (Nat.mul_dvd_mul h1 h2)
    have hprod : ((l₂.M * u : ℕ) : ℤ) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * ((l₂.M : ℕ) : ℤ) ^ (Module.finrank ℤ Dw.La * n) *
        (2 * NumberField.discr E * ((l₂.M * u : ℕ) : ℤ)) ^ d =
        K * (((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) *
          (pd * u) ^ d : ℕ) : ℤ) := by
      rw [hK, hl]
      push_cast
      ring
    have hfin : ((p ^ c * (k * ((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) *
        (pd * u) ^ d)) : ℕ) : ℤ) = (K.natAbs : ℤ) * (((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) *
          pd ^ (Module.finrank ℤ Dw.La * n) * (pd * u) ^ d : ℕ) : ℤ) := by
      rw [hKk]
      push_cast
      ring
    rw [hfin]
    refine dvd_trans ?_ (mul_dvd_mul_right hKd _)
    rw [← hprod]
    push_cast at h12 ⊢
    exact mul_dvd_mul h12 dvd_rfl

end GlobalTheory.ConstBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunction
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverComp

theorem forms_mul_comp : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ N : ℕ, 0 < N → C.d.l₂.M ∣ N → (WeberIn T.Q.H C.d.c₂.F N ∨ CurveOver T.Q.H C.d.c₂.F N) → ∀ w : GA D (T.V j σ) → C.d.c₂.F, (∀ h h' : GA D (T.V j σ), finHom (T.V j σ) h = finHom (T.V j σ) h' → w h = w h') → (∀ γ ∈ GQ (T.V j σ), ∀ h, w (γ * h) = w h) → (∀ u : GA D (T.V j σ), gLat (T.V j σ) u = latHat (T.V j σ) → FinCong (T.V j σ) C.d.l₂.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ φ ∈ C.ratForms a n, (fun h => C.σ₂ (w h) * φ h) ∈ C.ratForms a n) ∧ ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), (∀ la ∈ S, ∀ h, la.valuation C.d.c₂.F (w h) ≤ 1) → ∀ φ ∈ C.intForms a n S, (fun h => C.σ₂ (w h) * φ h) ∈ C.intForms a n S := by
  intro D T hL j hj σ hσ C hU N hN hMN hW w hw1 hw2 hw3 a n
  obtain ⟨hlev, hA, hinc, hUnf, hdom, hr, g, e, F, ik, φ, th, hmod, hth, hdict⟩ := hU
  have hpq := (GlobalTheory.Member.exists_iotaOK D T.Q hL.pins j hj).2
  have hpos : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hio := (GlobalTheory.TupleCover.iotaOK_and_frame T hL j hj σ hσ (T.V j σ) rfl hr).1
  have hgood : GoodEmb C.d.c₂ C.σ₂ := by
    have h1 := hσ
    rw [← hinc] at h1
    exact h1
  have hMN' : C.d.l₂.M' ∣ N := by
    simpa [Level.M', hA] using hMN
  have key := _root_.GlobalTheory.CompMul.sec_mul_of_weberIn D T.Q hL.pins j hj C.d.l₂ C.d.Xo₂ C.d.c₂ C.σ₂ (T.V j σ) D.R.r hr C.U₂ C.dict₂
    (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) g e F ik φ th (T.x₀ j σ) hio hpos hA hgood hmod hdict hdom
    hUnf N hN hMN' hW w hw1 hw2 hw3 a n
  have hrd : ∀ f f' : Rul C.d.Xo₂ C.d.c₂,
      (∀ h, rdU C.U₂ f' (C.dict₂ h).1 (C.dict₂ h).2 = C.σ₂ (w h) * rdU C.U₂ f (C.dict₂ h).1 (C.dict₂ h).2) →
      C.rd a f' = fun h => C.σ₂ (w h) * C.rd a f h := by
    intro f f' hff
    funext h
    simp only [Cover.rd, Pi.smul_apply, smul_eq_mul]
    change _ * (_ * rdU C.U₂ f' (C.dict₂ h).1 (C.dict₂ h).2) = _ * (_ * (_ * rdU C.U₂ f (C.dict₂ h).1 (C.dict₂ h).2))
    rw [hff h]
    ring
  refine ⟨?_, ?_⟩
  · rintro _ ⟨f, ⟨hf, hc⟩, rfl⟩
    obtain ⟨f', hf', h1, h2, -⟩ := key f hf
    exact ⟨f', ⟨hf', h2 _ hc⟩, hrd f f' h1⟩
  · rintro S hS _ ⟨f, ⟨⟨hf, hc⟩, hv⟩, rfl⟩
    obtain ⟨f', hf', h1, h2, h3⟩ := key f hf
    exact ⟨f', ⟨⟨hf', h2 _ hc⟩, fun la hla v hvv => h3 la (hS la hla) (hv la hla) v hvv⟩, hrd f f' h1⟩

end GlobalTheory.CoverComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MovedLevPoint
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace GlobalTheory.SingleDatum.MovedLevel

theorem cSep_mem {D : D7} {H : Geo.Tor.Host D.host.E} (l : Geo.Tor.Level H) :
    cSep l ∈ Mfr l ∧ cSep l - 1 ∈ l.Mb := by
  have hex : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb := by
    have : (1 : 𝓞 D.host.E) ∈ l.Mb ⊔ Mfr l := by rw [show l.Mb ⊔ Mfr l = ⊤ from l.coprime]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 this
    exact ⟨y, hy, by rw [← hxy, sub_add_cancel_right]; exact neg_mem hx⟩
  unfold cSep; rw [dite_eq_left hex]; exact hex.choose_spec

end GlobalTheory.SingleDatum.MovedLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PureTensorOTransSumLin
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SingleDatum

theorem pureTensorO_finsetSum {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {ι : Type} (s : Finset ι) (a : ι → ℂ)
    (g : ι → WO S T → ℂ) (hg : ∀ i, IsThetaFunO ψ S T (g i)) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsThetaFunO ψ S T (∑ i ∈ s, a i • g i) ∧
      pureTensorO ψ θ S T sS sT BS BT (∑ i ∈ s, a i • g i) φ =
        ∑ i ∈ s, a i • pureTensorO ψ θ S T sS sT BS BT (g i) φ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.OrientedHeis.theta_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (hg i)) ih.1, ?_⟩
    rw [GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (a i) (hg i) ih.1 φ, ih.2]

theorem pureTensorO_transSum_lin : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW s f₀ → ∀ (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → ∀ [Fintype (Fin V.rank → LevQ Dw l₂)] (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (w : (Fin V.rank → LevQ Dw l₂) → ℂ) (P : PolF D W.rank V.rank), pureTensorO ψ θ V W (fun _ => 1) s BV BW (transSum ψ V W l₂ ι e f₀ w) P = ∑ q, w q • pureTensorO ψ θ V W (fun _ => 1) s BV BW (transSum ψ V W l₂ ι e f₀ (fun q' => if q' = q then 1 else 0)) P := by
  intro D H Dw ψ θ V W χV χW om ΛV ΛW s f₀ hv ι l₂ e he _ BV BW w P
  have hψ : IsStdChar D ψ (-1) := hv.2.2.2.2.2.2.2.2.1
  have hθ : IsInfFam θ := hv.1.inf
  have hf₀ : IsThetaFunO ψ V W f₀ := hv.2.2.2.2.2.2.2.2.2.2
  have hinf : infPart D e = 0 := by
    obtain ⟨Q, hQ, -⟩ := he
    exact GlobalTheory.PlaceDatum.infPart_idemSum hQ
  have hpt : ∀ q, (levPoint V W l₂ ι e q).map (infPart D) = 0 := by
    intro q
    ext a b
    simp [levPoint, Matrix.map_apply, map_mul, hinf]
  have hth : ∀ q, IsThetaFunO ψ V W (heisO ψ V W (levPoint V W l₂ ι e q) f₀) := fun q =>
    ((GlobalTheory.FinTranslate.finite_translate D ψ θ V W hψ hθ f₀ hf₀).2 _ (hpt q)).1
  have key : ∀ w' : (Fin V.rank → LevQ Dw l₂) → ℂ,
      pureTensorO ψ θ V W (fun _ => 1) s BV BW (transSum ψ V W l₂ ι e f₀ w') P =
        ∑ q, (((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ * w' q) •
          pureTensorO ψ θ V W (fun _ => 1) s BV BW (heisO ψ V W (levPoint V W l₂ ι e q) f₀) P := by
    intro w'
    have h1 : transSum ψ V W l₂ ι e f₀ w' = ∑ q, (((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ * w' q) •
        heisO ψ V W (levPoint V W l₂ ι e q) f₀ := by
      unfold transSum
      rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_smul]
    rw [h1]
    exact (pureTensorO_finsetSum hψ hθ (fun _ => 1) BV s BW Finset.univ _ _ hth P).2
  rw [key w]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [key, Finset.sum_eq_single q]
  · rw [if_pos rfl, mul_one, mul_comm, ← smul_smul]
  · intro b _ hb
    rw [if_neg hb, mul_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ q) h

end GlobalTheory.SingleDatum

end
end

