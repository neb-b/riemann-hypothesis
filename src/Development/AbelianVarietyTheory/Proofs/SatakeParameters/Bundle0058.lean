module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0042
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
open Module TensorProduct

noncomputable section

namespace GlobalTheory.HTW.Rec

section Transport

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem finrank_eq_of_equiv_tensor {C : Type} [AddCommGroup C] [Module Qp C] (e : V ≃ₗ[LL] V')
    (S : Submodule LL (V ⊗[Qp] C)) (S' : Submodule LL (V' ⊗[Qp] C))
    (a : ∀ x ∈ S, SumJumps.ext1 Qp C e.toLinearMap x ∈ S')
    (b : ∀ x ∈ S', SumJumps.ext1 Qp C e.symm.toLinearMap x ∈ S) :
    finrank LL S = finrank LL S' := by
  have h1 : ∀ x : V ⊗[Qp] C, SumJumps.ext1 Qp C e.symm.toLinearMap
      (SumJumps.ext1 Qp C e.toLinearMap x) = x := by
    intro x
    rw [SumJumps.ext1_comp_ext1]
    convert SumJumps.ext1_id (LL := LL) x
    ext v; simp
  have h2 : ∀ x : V' ⊗[Qp] C, SumJumps.ext1 Qp C e.toLinearMap
      (SumJumps.ext1 Qp C e.symm.toLinearMap x) = x := by
    intro x
    rw [SumJumps.ext1_comp_ext1]
    convert SumJumps.ext1_id (LL := LL) x
    ext v; simp
  refine LinearEquiv.finrank_eq (LinearEquiv.ofLinear
    ((SumJumps.ext1 Qp C e.toLinearMap).restrict a)
    ((SumJumps.ext1 Qp C e.symm.toLinearMap).restrict b) ?_ ?_)
  · ext x
    simp [LinearMap.restrict_apply, h2]
  · ext x
    simp [LinearMap.restrict_apply, h1]

variable {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem symm_equivariant (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (g : G) (v : V') :
    e.symm.toLinearMap (ρ' g v) = ρ g (e.symm.toLinearMap v) := by
  apply e.injective
  rw [he]
  simp

theorem finrank_dcris_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    finrank LL (Dcris PD ρ) = finrank LL (Dcris PD ρ') :=
  finrank_eq_of_equiv_tensor e _ _ (SumJumps.dcris_map PD e.toLinearMap he)
    (SumJumps.dcris_map PD e.symm.toLinearMap (symm_equivariant e he))

theorem finrank_fildR_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (τ : K →ₐ[Qp] LL) (a : ℤ) :
    finrank LL (FildR PD ρ τ a) = finrank LL (FildR PD ρ' τ a) :=
  finrank_eq_of_equiv_tensor e _ _ (SumJumps.fildR_map PD e.toLinearMap he τ a)
    (SumJumps.fildR_map PD e.symm.toLinearMap (symm_equivariant e he) τ a)

theorem multV_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (τ : K →ₐ[Qp] LL) (a : ℤ) : multV PD ρ τ a = multV PD ρ' τ a := by
  simp only [multV, finrank_fildR_eq_of_equiv PD e he]

theorem isCrys_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (h : IsCrys PD ρ') : IsCrys PD ρ := by
  unfold IsCrys at h ⊢
  rw [finrank_dcris_eq_of_equiv PD e he, h, e.finrank_eq]

end Transport

theorem isCrys_multV_of_isMatRep {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL) {r : ℕ}
    (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (h : IsMatRep T M) :
    (IsCrys (P.PD K) (matRep M) → IsCrys (P.PD K) T.ρ) ∧
      ∀ τ u, multV (P.PD K) T.ρ τ u = multV (P.PD K) (matRep M) τ u := by
  obtain ⟨e, he⟩ := h
  have he' : ∀ g v, e (T.ρ g v) = matRep M g (e v) := by
    intro g v
    rw [he]
    simp [matRep, Matrix.toLinAlgEquiv'_apply]
  exact ⟨isCrys_of_equiv _ e he', fun τ u => multV_eq_of_equiv _ e he' τ u⟩

end GlobalTheory.HTW.Rec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharMulInvEqOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory

namespace RowTypeInv

open Formalism.L2.Col.Loc Formalism.L2.Col.LocE

section Alg

variable {R : Type*} [CommRing R]

end Alg

section Red

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_one : IntAt P (1 : E) := by simpa using IntAt.coe P 1

theorem intAt_zero : IntAt P (0 : E) := by simpa using IntAt.coe P 0

theorem reduction_one₂ : redP P (1 : E) = 1 := by simpa using reduction_coe P 1

theorem reduction_zero : redP P (0 : E) = 0 := by simpa using reduction_coe P 0

def intRing : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := IntAt.mul
  one_mem' := intAt_one P
  add_mem' := IntAt.add
  zero_mem' := intAt_zero P
  neg_mem' := fun {a} ha => by
    have := (IntAt.coe P (-1)).mul ha
    simpa using this

noncomputable def redHom : intRing P →+* 𝓞 E ⧸ P.asIdeal where
  toFun a := redP P a.1
  map_one' := reduction_one₂ P
  map_mul' a b := reduction_mul a.2 b.2
  map_zero' := reduction_zero P
  map_add' a b := reduction_add a.2 b.2

theorem reduction_sum₂ {ι : Type*} (s : Finset ι) (f : ι → E) (hf : ∀ i, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  have h := map_sum (redHom P) (fun i => (⟨f i, hf i⟩ : intRing P)) s
  have h2 : ((∑ i ∈ s, (⟨f i, hf i⟩ : intRing P) : intRing P) : E) = ∑ i ∈ s, f i := by
    simp
  rw [← h2]
  exact h

theorem reduction_det {t : ℕ} (A : Matrix (Fin t) (Fin t) E) (hA : ∀ i j, IntAt P (A i j)) :
    redP P A.det = (Matrix.of fun i j => redP P (A i j)).det := by
  let B : Matrix (Fin t) (Fin t) (intRing P) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have h1 : (B.det : E) = A.det := by
    have := (intRing P).subtype.map_det B
    exact this
  have h2 := (redHom P).map_det B
  rw [← h1]
  exact h2


end Red

section Ent

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

theorem mem_sclLat (N : ℕ) (e : ℕ → ℤ) (v : Sp E N) :
    v ∈ sclLat P q N e ↔ ∀ l : Fin N, IntAt P (((q : E) ^ e l.1)⁻¹ * v l) := by
  unfold sclLat stdAt
  rw [Submodule.mem_comap, mem_localization_standardLattice]
  simp



variable {P q} {k₀ r t n : ℕ} {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)}

end Ent

end RowTypeInv


end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaQuotientCharMulInvEqOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.TwistRowType

variable {E : Type} [Field E] [NumberField E]

def intSub (P : HeightOneSpectrum (𝓞 E)) : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := IntAt.mul
  one_mem' := by simpa using IntAt.coe P 1
  add_mem' := IntAt.add
  zero_mem' := by simpa using IntAt.coe P 0
  neg_mem' := fun {a} ha => by
    have h := IntAt.mul (IntAt.coe P (-1)) ha
    simpa using h

def redHom (P : HeightOneSpectrum (𝓞 E)) : intSub P →+* 𝓞 E ⧸ P.asIdeal where
  toFun a := redP P a.1
  map_one' := by simpa using reduction_coe P 1
  map_mul' a b := reduction_mul a.2 b.2
  map_zero' := by simpa using reduction_coe P 0
  map_add' a b := reduction_add a.2 b.2

theorem redHom_apply (P : HeightOneSpectrum (𝓞 E)) (a : intSub P) : redHom P a = redP P a.1 := rfl

variable [StarRing E]

theorem mem_stdAt (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (x : Sp E n) :
    x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := mem_localization_standardLattice P x

theorem eN_mem (P : HeightOneSpectrum (𝓞 E)) (N i : ℕ) : Loc.eN E N i ∈ stdAt E N P := by
  rw [mem_stdAt]
  intro j
  unfold Loc.eN
  split_ifs
  · simpa using IntAt.coe P 1
  · simpa using IntAt.coe P 0

theorem intAt_entry (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} {g : Sp E N ≃ₗ[E] Sp E N}
    (hg : g ∈ stabL E N (stdAt E N P)) (i j : ℕ) : IntAt P (Loc.atN (g (Loc.eN E N j)) i) := by
  have hg' : ∀ x, g x ∈ stdAt E N P ↔ x ∈ stdAt E N P := hg
  have hm : g (Loc.eN E N j) ∈ stdAt E N P := (hg' _).2 (eN_mem P N j)
  rw [mem_stdAt] at hm
  unfold Loc.atN
  split_ifs with h
  · exact hm _
  · simpa using IntAt.coe P 0

def blockD (P : HeightOneSpectrum (𝓞 E)) (kj n : ℕ) {N : ℕ} {g : Sp E N ≃ₗ[E] Sp E N}
    (hg : g ∈ stabL E N (stdAt E N P)) : Matrix (Fin (n - kj)) (Fin (n - kj)) (intSub P) :=
  Matrix.of fun s t => ⟨Loc.atN (g (Loc.eN E N (kj + t.1))) (kj + s.1), intAt_entry P hg _ _⟩

theorem redP_det_block (P : HeightOneSpectrum (𝓞 E)) (kj n : ℕ) {N : ℕ} {g : Sp E N ≃ₗ[E] Sp E N}
    (hg : g ∈ stabL E N (stdAt E N P)) :
    redP P (Matrix.det (Matrix.of fun s t : Fin (n - kj) =>
      Loc.atN (g.toLinearMap (Loc.eN E N (kj + t.1))) (kj + s.1))) =
      ((redHom P).mapMatrix (blockD P kj n hg)).det := by
  have h1 : (Matrix.of fun s t : Fin (n - kj) =>
      Loc.atN (g.toLinearMap (Loc.eN E N (kj + t.1))) (kj + s.1)) =
      (intSub P).subtype.mapMatrix (blockD P kj n hg) := by
    ext s t
    rfl
  rw [h1, ← RingHom.map_det, ← RingHom.map_det]
  rfl

end GlobalTheory.TwistRowType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeWindowEnds
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

theorem wB_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ wB L := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    positivity
  have h0 : 0 ≤ L.sc.w'' D.R.n := by unfold Scale.w''; positivity
  have h1 := L.etaSz_pos
  exact le_trans (by linarith) (le_max_left _ _)

theorem floor_size_le_wB {D : D7} (L : SizeData₂ D) (g : D.R.GG) (j : Fin D.R.m) (hg : ¬ Thick D.host g) :
    ((⌊(hcAt D g).e j⌋.toNat : ℕ) : ℝ) ≤ wB L := by
  set ρ := D.eTau.symm ⟨plc g, plc_mem g⟩ with hρ
  have hρ' : (D.eTau ρ : D.R.GG) = plc g := by rw [hρ, Equiv.apply_symm_apply]
  have hj : j.1 + 1 ≤ D.R.m := j.2
  have hw : wj D (j.1 + 1) ρ = (((D.hc ρ).e j : ℚ) : ℝ) := by
    have hj' : j.1 + 1 - 1 < D.R.m := by have := j.2; omega
    rw [wj, dite_eq_left hj']
    have : (⟨j.1 + 1 - 1, hj'⟩ : Fin D.R.m) = j := Fin.ext (by simp)
    rw [this]
  have hthick : (D.eTau ρ : D.R.GG) ∉ D.host.thickPlaces := by rw [hρ']; exact hg
  have key : wj D (j.1 + 1) ρ ≤ wB L := by
    by_cases h2 : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht', e⟩ := Finset.mem_image.mp h2
      have a := (L.win_top _ (by omega) hj ρ ⟨t, ht'⟩ e.symm).2
      have b : (L.bT (⟨t, ht'⟩ : D.host.TT) : ℝ) ≤ ⨆ t : D.host.TT, (L.bT t : ℝ) :=
        le_ciSup (f := fun t : D.host.TT => (L.bT t : ℝ)) (Set.finite_range _).bddAbove ⟨t, ht'⟩
      exact le_trans (by linarith) (le_max_right _ _)
    · have a := (L.win_thin (j.1 + 1) (by omega) hj ρ ⟨(D.eTau ρ).2, h2, hthick⟩).2
      exact le_trans a (le_max_left _ _)
  rw [hw] at key
  have he : (hcAt D g).e j = (D.hc ρ).e j := rfl
  rw [he]
  rcases le_or_gt 0 ⌊(D.hc ρ).e j⌋ with h | h
  · rw [show ((⌊(D.hc ρ).e j⌋.toNat : ℕ) : ℝ) = ((⌊(D.hc ρ).e j⌋ : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg h]
    have := Int.floor_le ((D.hc ρ).e j)
    have : (((⌊(D.hc ρ).e j⌋ : ℤ) : ℚ) : ℝ) ≤ (((D.hc ρ).e j : ℚ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  · rw [Int.toNat_eq_zero.2 h.le]
    simpa using wB_nonneg L

theorem wMax_le_wB : ∀ {D : D7} (L : SizeData₂ D), (wMax D : ℝ) ≤ wB L ∧ (wHat D : ℝ) ≤ wP L := by
  intro D L
  have hB := wB_nonneg L
  have h1 : wMax D ≤ ⌊wB L⌋₊ := by
    apply csSup_le'
    rintro s ⟨g, j, hg, rfl⟩
    exact Nat.le_floor (floor_size_le_wB L g j hg)
  have h2 : (wMax D : ℝ) ≤ wB L :=
    le_trans (by exact_mod_cast h1) (Nat.floor_le hB)
  refine ⟨h2, ?_⟩
  have h3 : (((D.R.t + 1) / 2 : ℕ) : ℝ) ≤ ((D.R.t : ℝ) + 1) / 2 := by
    have := Nat.cast_div_le (α := ℝ) (m := D.R.t + 1) (n := 2)
    push_cast at this
    exact this
  unfold wHat wP
  push_cast
  linarith

end GlobalTheory.HTW.Rec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OneLeScOfSizeData
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem one_le_Sc {D : D7} (L : SizeData₂ D) : (1 : ℝ) ≤ L.Sc := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  set τ := D.eTau.symm ⟨plc (1 : D.R.GG), plc_mem 1⟩
  set P := D.hc τ
  have h1 := P.u_gt_v ⟨1, by omega⟩
  have h2 := P.v_gt_u ⟨0, by omega⟩
  obtain ⟨z0, hz0⟩ := P.v_int ⟨0, by omega⟩
  obtain ⟨z1, hz1⟩ := P.v_int ⟨1, by omega⟩
  have c0 := (L.cloud_v τ ⟨0, by omega⟩).2
  have c1 := (L.cloud_v τ ⟨1, by omega⟩).1
  simp only at h1 h2
  have hlt : P.v ⟨1, by omega⟩ < P.v ⟨0, by omega⟩ := lt_trans h1 h2
  rw [hz0, hz1] at hlt
  have hz : z1 < z0 := by exact_mod_cast hlt
  have hz1' : (0 : ℝ) ≤ (z1 : ℝ) := by
    have : (((P.v ⟨1, by omega⟩ : ℚ) : ℝ)) = (z1 : ℝ) := by rw [hz1]; push_cast; rfl
    rw [← this]; exact c1
  have hz0' : (z0 : ℝ) ≤ L.Sc := by
    have : (((P.v ⟨0, by omega⟩ : ℚ) : ℝ)) = (z0 : ℝ) := by rw [hz0]; push_cast; rfl
    rw [← this]; exact c0
  have : (0 : ℤ) ≤ z1 := by exact_mod_cast hz1'
  have : (1 : ℝ) ≤ (z0 : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ z0 by omega)
  linarith

theorem recWord_small_pos : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ →
    Small (recWord L j ε g) ∧ 1 ≤ (recWord L j ε g).S ∧ 1 ≤ (recWord L j ε g).η := by
  intro D L C j ε n g ψ hR _
  have hB := _root_.GlobalTheory.HTW.pageWord_box L C j ε (1 : D.R.GG) (1 : D.R.GG) hR
  obtain ⟨b1, w1, bw, bη, bS, hsz⟩ := hB
  refine ⟨⟨b1, w1, bw, bη, bS, fun a => ?_⟩, ?_, ?_⟩
  · have hB' := _root_.GlobalTheory.HTW.pageWord_box L C j ε (g a) (1 : D.R.GG) hR
    have h := hB'.2.2.2.2.2 (0 : ZMod (orderOf (1 : D.R.GG)))
    simp only [pageWord, letter, one_pow, mul_one] at h
    show etaHat L < (szT (hcAt D (g a)) j (pos ε (g a))).toNat
    exact Int.lt_toNat.mpr h
  · show 1 ≤ sHat L
    unfold sHat
    exact Nat.le_floor (by exact_mod_cast one_le_Sc L)
  · show 1 ≤ etaHat L
    unfold etaHat; omega

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThickLetterWordHypothesesOfCommonConditions
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem setting_of_wordBase : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)), D.nd.l i ≠ 2 → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → RecS.ThickLetterWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd := by
  intro D L HW i r ρ π w hw Cx hG Wd hl hB _ft T₁ T₂ F h1 h2 hF
  obtain ⟨ht1c, ht1w, ht1l⟩ := hB.t1 T₁ h1
  obtain ⟨ht2c, ht2low⟩ := hB.t2 T₂ h2
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨ht1c, ht2c, hF⟩, hB.small.1.2.2.2.2.2, ?_, fun a => ht2low _ft a, ?_, ht1l⟩
  · intro x y hxy
    have hv : ((algebraMap ↥(Loc.K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1 x : ↥(D.nbr i w hw).Kw.1) : Loc.Om (D.nd.l i)) =
        ((algebraMap ↥(Loc.K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1 y : ↥(D.nbr i w hw).Kw.1) : Loc.Om (D.nd.l i)) := by rw [hxy]
    exact Subtype.ext hv
  · intro y
    exact ⟨⟨y.1, show y.1 ∈ Loc.K0 (D.nbr i w hw).Kw from ⟨y.2, hB.unram y.2⟩⟩, Subtype.ext rfl⟩
  · exact (HW _).W_s _ 1 _ hG
  · rw [(D.loc _).PD_p]; exact hl
  · intro a
    have hw' := ht1w a
    have e : Wd.win a = (if Wd.up a then
        Set.Icc (Wd.sz a : ℤ) ((Wd.sz a : ℤ) + Wd.S) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η
      else Set.Icc (-(Wd.sz a : ℤ) - Wd.S) (-(Wd.sz a : ℤ)) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η) := by
      unfold NWord.win
      cases h : Wd.up a <;> ext u <;> simp [abs_le]
    rw [← e]; exact hw'
  · intro a ha
    rcases hB.num.thick_or a with h | h
    · exact absurd h ha
    · exact h

end GlobalTheory.HTW.RecS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordConjHypATAllThickStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualOrbitPageWord_conj_hypAT_allThick : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → Thick D.host τ → (pageWord L j ε τ (D.R.cc)).HypAT l ∧ ∀ i, (pageWord L j ε τ (D.R.cc)).thick i := by
  first | exact @GlobalTheory.HTW.conjWord_hypAT | exact GlobalTheory.HTW.conjWord_hypAT | (intros; apply GlobalTheory.HTW.conjWord_hypAT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordJumpsInWindows
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_T1_and_J1_mem_window_of_roomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T1 ∧ ∀ i, ∀ u ∈ (pageWord L j ε τ φ).J1 i, -((pageWord L j ε τ φ).Mi i : ℤ) ≤ u ∧ u ≤ (pageWord L j ε τ φ).hi i := by
  intro D L C j ε τ φ hR
  have hT : (pageWord L j ε τ φ).T1 := by
    intro i u hu
    exact _root_.GlobalTheory.jT1_mem_window_of_bounded_v (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) L.Sc L.etaSz
      (fun a => L.cloud_v _ a) (fun a => L.be_close _ a j) u hu
  refine ⟨hT, GlobalTheory.T.jumps_mem_box_neg_M_h _ (fun i => ?_) hT⟩
  have h := (_root_.GlobalTheory.HTW.pageWord_box L C j ε τ φ hR).2.2.2.2.2 i
  exact le_trans (Int.natCast_nonneg _) h.le

end GlobalTheory.HTW
end

