module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0065
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointRegular
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegPhi

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem sum_mapDomain_block {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : ∀ p, (v p).1 = κ p.1)
    (m : (Σ k, ι k) →₀ ℕ) (k' : K') :
    ∑ i, (Finsupp.mapDomain v m) ⟨k', i⟩ = ∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0 := by
  have e1 : ∀ q : (Σ k, ι' k) →₀ ℕ, ∑ i, q ⟨k', i⟩ = q.sum (fun r x => if r.1 = k' then x else 0) := by
    intro q
    rw [Finsupp.sum_fintype _ _ (fun r => by simp), Fintype.sum_sigma,
      Finset.sum_eq_single k' (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have e2 : ∑ p : Σ k, ι k, (if κ p.1 = k' then m p else 0) = m.sum (fun p x => if κ p.1 = k' then x else 0) := by
    rw [Finsupp.sum_fintype _ _ (fun r => by simp)]
  rw [e1, e2, Finsupp.sum_mapDomain_index (fun r => by simp) (fun r a b => by split_ifs <;> simp)]
  simp only [hv]

theorem isMultiHomog_rename_block {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v) {f : MRing ι}
    {b : K → ℕ} (hf : IsMultiHomog f b) : IsMultiHomog (rename v f) (Function.extend κ b 0) := by
  intro m hm k'
  rw [support_rename_of_injective hb.2.1, Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  rw [sum_mapDomain_block hb.2.2.1]
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hb.1.extend_apply, ← hf m0 hm0 k]
    simp only [hb.1.eq_iff]
    rw [Fintype.sum_sigma, Finset.sum_eq_single k (fun b _ hb' => by simp [hb']) (by simp)]
    simp
  · rw [Function.extend_apply' _ _ _ hk, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg (fun h => hk ⟨p.1, h⟩)]

theorem mConeMap_rename {Ω : Type} [Field Ω] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v)
    (y : (Σ k, ι' k) → Ω) (g : MRing ι) : mConeMap y (rename v g) = rename κ (mConeMap (y ∘ v) g) := by
  simp only [mConeMap]
  rw [aeval_rename]
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    simp [hp, hq]
  | mul_X p i hp =>
    simp [hp, hb.2.2.1 i]

theorem mConeMap_comp {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) (g : MRing ι) :
    mConeMap (φ ∘ x) g = map φ (mConeMap x g) := by
  simp only [mConeMap]
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul]
    rw [hp]
    simp only [aeval_X, Function.comp_apply, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

theorem aeval_comp_ringHom {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) (g : MRing ι) :
    aeval (φ ∘ x) g = φ (aeval x g) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, aeval_X, Function.comp_apply]

theorem eval_rename_block (v : (Σ k, ι k) → Σ k, ι' k) (z : (Σ k, ι' k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename v f)) = eval (z ∘ v) (map (Int.castRingHom ℂ) f) := by
  rw [map_rename, eval_rename]

theorem rename_notMem {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v)
    {z : (Σ k, ι' k) → ℂ} {h : MRing ι} (hn : h ∉ mCoordIdeal (z ∘ v)) : rename v h ∉ mCoordIdeal z := by
  intro hmem
  apply hn
  rw [mCoordIdeal, RingHom.mem_ker] at hmem ⊢
  rw [mConeMap_rename hb] at hmem
  exact rename_injective κ hb.1 (by rw [hmem, map_zero])

theorem comp_mem_mcPts {Ω Ω' : Type} [Field Ω] [Field Ω'] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k}
    (hb : IsBlockMap κ v) (φ : Ω →+* Ω') {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (hx : x' ∘ v = φ ∘ x)
    {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x')) : z ∘ v ∈ mcPts (mCoordIdeal x) := by
  unfold mcPts at hz ⊢
  simp only [Set.mem_ofPred_eq] at hz ⊢
  obtain ⟨hz1, hz2⟩ := hz
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i', hi'⟩ := hz1 (κ k)
    obtain ⟨⟨k0, i⟩, hp⟩ := hb.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have h0 := hb.2.2.1 ⟨k0, i⟩
    rw [hp] at h0
    have hk0 : k0 = k := hb.1 h0.symm
    subst hk0
    refine ⟨i, ?_⟩
    show z (v ⟨k0, i⟩) ≠ 0
    rw [hp]
    exact hi'
  · rw [← eval_rename_block v z f]
    apply hz2
    rw [mCoordIdeal, RingHom.mem_ker] at hf ⊢
    rw [mConeMap_rename hb, hx, mConeMap_comp, hf, map_zero, map_zero]

end Forms

private theorem isHecke_div_and_resEtaPow_div {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    mConeMap y g = C (aeval y g) * ∏ k, X k ^ d k := by
  have key : ∀ m ∈ g.support, (m.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e) = ∏ k, X k ^ d k := by
    intro m hm
    rw [Finsupp.prod_fintype _ _ (fun p => pow_zero _), Fintype.prod_sigma]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [← key m hm]
  simp only [mConeMap, aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_mul, map_prod,
    map_pow, algebraMap_int_eq, eq_intCast, map_intCast]
  ring

private theorem isPair_and_isPair_of_isTriple {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {v1 v2 : ℂ}
    (H1 : IsValueAt y s z v1) (H2 : IsValueAt y s z v2) : v1 = v2 := by
  obtain ⟨d1, g1, h1, hg1, hh1, -, he1, hz1, rfl⟩ := H1
  obtain ⟨d2, g2, h2, hg2, hh2, -, he2, hz2, rfl⟩ := H2
  have hmem : g1 * h2 - g2 * h1 ∈ mCoordIdeal y := by
    rw [mCoordIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, isHecke_div_and_resEtaPow_div y hg1, isHecke_div_and_resEtaPow_div y hh2, isHecke_div_and_resEtaPow_div y hg2,
      isHecke_div_and_resEtaPow_div y hh1, he1, he2]
    simp only [map_mul]
    ring
  unfold mcPts at hz
  obtain ⟨-, hzP⟩ := hz
  have h0 := hzP _ hmem
  simp only [map_sub, map_mul] at h0
  rw [div_eq_div_iff hz1 hz2]
  linear_combination h0

theorem regAt_φ_valAt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ) (s : M.Ω), zb ∈ mcPts (mCoordIdeal M'.x) → RegAt M.x (mCoordIdeal (zb ∘ Cv.v)) s → RegAt M'.x (mCoordIdeal zb) (Cv.φ s) ∧ valAt M'.x (Cv.φ s) zb = valAt M.x s (zb ∘ Cv.v) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb s hzb hreg
  obtain ⟨d, g, h, hg, hh, hhn, he⟩ := hreg
  have hb := Cv.block
  have hxv : M'.x ∘ Cv.v = Cv.φ ∘ M.x := funext Cv.x_eq
  have hz' : zb ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) := comp_mem_mcPts hb Cv.φ hxv hzb
  have hg' := isMultiHomog_rename_block hb hg
  have hh' := isMultiHomog_rename_block hb hh
  have hhn' := rename_notMem hb hhn
  have hae : ∀ f : MRing (baseIdx ι M.blk), aeval M'.x (rename Cv.v f) = Cv.φ (aeval M.x f) := by
    intro f
    rw [aeval_rename, hxv, aeval_comp_ringHom]
  have he' : aeval M'.x (rename Cv.v g) = Cv.φ s * aeval M'.x (rename Cv.v h) := by
    rw [hae, hae, he, map_mul]
  refine ⟨⟨_, _, _, hg', hh', hhn', he'⟩, ?_⟩
  have hcast : ∀ (w : (Σ k, baseIdx ι M.blk k) → ℂ) (f : MRing (baseIdx ι M.blk)),
      eval w (map (Int.castRingHom ℂ) f) = aeval w f := by
    intro w f
    rw [eval_map, aeval_def, algebraMap_int_eq]
  have hev : eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h) ≠ 0 := by
    intro h0
    apply hhn
    rw [mCoordIdeal, RingHom.mem_ker, isHecke_div_and_resEtaPow_div _ hh, ← hcast, h0, map_zero, zero_mul]
  have hax : aeval M.x h ≠ 0 := by
    intro h0
    have hmem : h ∈ mCoordIdeal M.x := by
      rw [mCoordIdeal, RingHom.mem_ker, isHecke_div_and_resEtaPow_div _ hh, h0, map_zero, zero_mul]
    have hz2 := hz'
    unfold mcPts at hz2
    exact hev (hz2.2 _ hmem)
  have hv1 : IsValueAt M.x s (zb ∘ Cv.v)
      (eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) g) / eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h)) :=
    ⟨d, g, h, hg, hh, hax, he, hev, rfl⟩
  have hv2 : IsValueAt M'.x (Cv.φ s) zb
      (eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) g) / eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h)) := by
    refine ⟨_, _, _, hg', hh', ?_, he', ?_, ?_⟩
    · rw [hae]
      exact (map_ne_zero Cv.φ).2 hax
    · rw [eval_rename_block]
      exact hev
    · rw [eval_rename_block, eval_rename_block]
  have hex1 : ∃ v, IsValueAt M.x s (zb ∘ Cv.v) v := ⟨_, hv1⟩
  have hex2 : ∃ v, IsValueAt M'.x (Cv.φ s) zb v := ⟨_, hv2⟩
  unfold valAt
  rw [dite_eq_left hex1, dite_eq_left hex2, isPair_and_isPair_of_isTriple hzb hex2.choose_spec hv2, isPair_and_isPair_of_isTriple hz' hex1.choose_spec hv1]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegPhi
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTransferIdealEq
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def coneOver {A : Type} [CommRing A] (Y : (Σ k, ι k) → A) : MRing ι →ₐ[ℤ] MvPolynomial K A :=
  aeval fun p => C (Y p) * X p.1

def scaleBy {F : Type} [Field F] (c : K → F) : MvPolynomial K F →ₐ[F] MvPolynomial K F :=
  aeval fun k => C (c k) * X k

omit [Fintype K] in
theorem scaleBy_injective {F : Type} [Field F] (c : K → F) (hc : ∀ k, c k ≠ 0) :
    Function.Injective (scaleBy c) := by
  have h : (scaleBy fun k => (c k)⁻¹).comp (scaleBy c) = AlgHom.id F _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [scaleBy, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]
    rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  exact Function.LeftInverse.injective (g := scaleBy fun k => (c k)⁻¹) fun f => DFunLike.congr_fun h f

theorem mConeMap_eq {A F : Type} [CommRing A] [Field F] (f : A →+* F) (Y : (Σ k, ι k) → A) (z : (Σ k, ι k) → F)
    (c : K → F) (hz : ∀ q, z q = c q.1 * f (Y q)) (p : MRing ι) :
    mConeMap z p = scaleBy c (MvPolynomial.map f (coneOver Y p)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [mConeMap, coneOver]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p q hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp]
    congr 1
    simp only [mConeMap, coneOver, aeval_X, scaleBy, map_mul, map_C, map_X, algHom_C, algebraMap_eq, hz q]
    ring

theorem mCoordIdeal_eq {A F : Type} [CommRing A] [Field F] (f : A →+* F) (hf : Function.Injective f)
    (Y : (Σ k, ι k) → A) (z : (Σ k, ι k) → F) (c : K → F) (hc : ∀ k, c k ≠ 0)
    (hz : ∀ q, z q = c q.1 * f (Y q)) : mCoordIdeal z = RingHom.ker (coneOver Y) := by
  ext p
  rw [mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker, mConeMap_eq f Y z c hz]
  constructor
  · intro h
    have h1 : MvPolynomial.map f (coneOver Y p) = 0 := scaleBy_injective c hc (by rw [h, map_zero])
    exact MvPolynomial.map_injective f hf (by rw [h1, map_zero])
  · intro h
    rw [h, map_zero, map_zero]

theorem map_minorIJ {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S) (h : Matrix (Fin N) (Fin N) R)
    (I J : Finset (Fin N)) : f (minorIJ h I J) = minorIJ (h.map f) I J := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]
    rfl
  · exact map_zero f

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

def polyPt (M : FlagModel y Ψ N j) : (Σ k, ι k) → MvPolynomial (LowIdx Ψ N j) M.Ω := fun q =>
  if h : ∀ p, M.blk p ≠ some q.1 then C (M.x ⟨⟨q.1, h⟩, q.2⟩)
  else ∑ I, C (M.coef q I) * minorIJ (genLow M.Ω N j (stepOf M q.1 h).1) I (stepCols N j (stepOf M q.1 h).2)

theorem exists_scale (M : FlagModel y Ψ N j) {F : Type} [Field F] (f : MvPolynomial (LowIdx Ψ N j) M.Ω →+* F)
    (ψ : M.Ω →+* F) (hfC : ∀ a, f (C a) = ψ a) (G B : Ψ → Matrix (Fin N) (Fin N) F)
    (hG : ∀ τ, IsBlockDiag j (G τ))
    (hB : ∀ τ, IsBlockDiag j (B τ) ∧ (B τ).BlockTriangular id ∧ IsLowerUni (G τ * B τ))
    (hf : ∀ q : LowIdx Ψ N j, f (X q) = (G q.1.1 * B q.1.1) q.1.2.1 q.1.2.2)
    (z : (Σ k, ι k) → F)
    (hbase : ∀ q : Σ k, baseIdx ι M.blk k, z ⟨q.1.1, q.2⟩ = ψ (M.x q))
    (hstep : ∀ p k, M.blk p = some k → ∀ m : ι k,
      z ⟨k, m⟩ = ∑ I, ψ (M.coef ⟨k, m⟩ I) * minorIJ (G p.1) I (stepCols N j p.2)) :
    ∃ c : K → F, (∀ k, c k ≠ 0) ∧ ∀ q, z q = c q.1 * f (polyPt M q) := by
  have hmap : ∀ τ, (genLow M.Ω N j τ).map f = G τ * B τ :=
    genLow_map f (H := fun τ => G τ * B τ) (fun τ => ⟨(hG τ).mul (hB τ).1, (hB τ).2.2⟩) hf
  have hdiag : ∀ τ c, B τ c c ≠ 0 := fun τ c h0 => by
    have h1 : (G τ).det * (B τ).det = 1 := by rw [← det_mul, (hB τ).2.2.det]
    have h2 : ∏ i, B τ i i = 0 := Finset.prod_eq_zero (Finset.mem_univ c) h0
    rw [det_of_upperTriangular (hB τ).2.1, h2, mul_zero] at h1
    exact zero_ne_one h1
  let s : Ψ × Fin N → F := fun p => ∏ c ∈ stepCols N j p.2, B p.1 c c
  have hs : ∀ p, s p ≠ 0 := fun p => Finset.prod_ne_zero_iff.2 fun c _ => hdiag p.1 c
  have gen : ∀ a b t : F, t ≠ 0 → a * b = t⁻¹ * (a * (b * t)) := fun a b t ht => by field_simp
  refine ⟨fun k => if h : ∀ p, M.blk p ≠ some k then 1 else (s (stepOf M k h))⁻¹, fun k => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · exact one_ne_zero
    · exact inv_ne_zero (hs _)
  · rintro ⟨k, m⟩
    by_cases h : ∀ p, M.blk p ≠ some k
    · have e := hbase ⟨⟨k, h⟩, m⟩
      simp only [polyPt, dif_pos h, one_mul, hfC]
      exact e
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [polyPt, dif_neg h, map_sum, map_mul, hfC, map_minorIJ, hmap]
      rw [hstep _ k (blk_stepOf M k h) m, Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [(_root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main F N j (stepOf M k h).2 M.j_le).2.2.1 _ _ I (hB _).1 (hB _).2.1]
      exact gen _ _ _ (hs _)

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackFirst
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt

theorem eq_on_block {K : Type} {ι : K → Type} {Kk : Type} {ιk : Kk → Type} {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) {a b : (Σ k, ι k) → ℂ} (h : a ∘ v = b ∘ v)
    {k : K} (hk : k ∈ Set.range κ) (m : ι k) : a ⟨k, m⟩ = b ⟨k, m⟩ := by
  obtain ⟨q, hq⟩ := hb.2.2.2 ⟨k, m⟩ hk
  rw [← hq]
  exact congrFun h q

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ (x y' : R.X) (z : (Σ k, ι k) → ℂ), y' ∈ R.U x → pr y' ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z ∘ v = R.lift x y' → stepPh M BM p v R pr y' = stepGap M BM p z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr H x y' z hy' hpr hz hzv
  obtain ⟨hb, hr, -, H1⟩ := H
  obtain ⟨z₀, hz₀, hz₀v, hz₀o⟩ := H1 y'
  have hex : pr y' ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift y' y' :=
    ⟨hpr, z₀, hz₀, hz₀v⟩
  have hph : stepPh M BM p v R pr y' = stepGap M BM p hex.2.choose := by
    unfold stepPh
    rw [dite_eq_left hex]
  obtain ⟨hz₁, hz₁v⟩ := hex.2.choose_spec
  rw [hph]
  generalize hex.2.choose = z₁ at hz₁ hz₁v

  have hbase : ∀ {a b : (Σ k, ι k) → ℂ}, a ∘ v = b ∘ v → basePart M.blk a = basePart M.blk b := by
    intro a b hab
    funext q
    exact eq_on_block hb hab (hr q.1.1 (Or.inl q.1.2)) q.2
  have hz₁o : SameOrbit (basePart M.blk z₁) (BM.Rb.lift (pr y') (pr y')) := by
    rw [hbase (hz₁v.trans hz₀v.symm)]
    exact hz₀o

  obtain ⟨c, hc, hcl⟩ := R.compat x y' y' ⟨hy', R.mem_U y'⟩
  set c' : K → ℂ := Function.extend κ c 1 with hc'
  have hc'0 : ∀ k, c' k ≠ 0 := by
    intro k
    by_cases hk : ∃ a, κ a = k
    · obtain ⟨a, rfl⟩ := hk
      rw [hc', hb.1.extend_apply]
      exact hc a
    · rw [hc', Function.extend_apply' _ _ _ hk]
      exact one_ne_zero
  set z₂ : (Σ k, ι k) → ℂ := fun q => c' q.1 * z₁ q with hz₂
  have hz₂m : z₂ ∈ mcPts (mCoordIdeal y) :=
    ((GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main K ι Φ y z₁ c' hc'0).2 hz₁).1
  have hz₂v : z₂ ∘ v = z ∘ v := by
    rw [hzv, hcl]
    funext q
    have h1 : z₁ (v q) = R.lift y' y' q := congrFun hz₁v q
    have h2 : c' (v q).1 = c q.1 := by
      rw [hb.2.2.1 q, hc', hb.1.extend_apply]
    simp only [Function.comp, hz₂, h1, h2]
  have ht : stepGap M BM p z₂ = stepGap M BM p z₁ :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_torus K ι Φ y Ψ N j M n BM p z₁ c' hc'0 hz₁.1
  have hz₂o : SameOrbit (basePart M.blk z₂) (BM.Rb.lift (pr y') (pr y')) := by
    obtain ⟨d, hd, hdl⟩ := hz₁o
    refine ⟨fun k => c' k.1 * d k, fun k => mul_ne_zero (hc'0 _) (hd k), ?_⟩
    funext q
    have h1 : basePart M.blk z₁ q = d q.1 * BM.Rb.lift (pr y') (pr y') q := congrFun hdl q
    have h2 : basePart M.blk z₂ q = c' q.1.1 * basePart M.blk z₁ q := rfl
    rw [h2, h1, mul_assoc]
  have hg : stepGap M BM p z₂ = stepGap M BM p z :=
    _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_eq_of_base_block K ι Φ y Ψ N j M n BM p (pr y') z₂ z hpr hz₂m hz hz₂o (hbase hz₂v)
      (fun k hk m => eq_on_block hb hz₂v (hr k (Or.inr hk)) m)
  rw [← ht, hg]

end GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBasesLinearIndependentSpan
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem basis_image {Ω M N ι : Type} [Field Ω] [AddCommGroup M] [Module Ω M] [AddCommGroup N] [Module Ω N]
    (b : Module.Basis ι Ω M) (f : M →ₗ[Ω] N) (hf : Function.Injective f) :
    LinearIndependent Ω (fun a => f (b a)) ∧
      Submodule.span Ω (Set.range fun a => f (b a)) = (⊤ : Submodule Ω M).map f := by
  refine ⟨b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf), ?_⟩
  have h : (Set.range fun a => f (b a)) = f '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [h, Submodule.span_image, b.span_eq]

theorem inW_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω} (A : HodgeCpt Y S x) :
    Function.Injective (inW A) :=
  LinearMap.inl_injective

theorem inO_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω} (A : HodgeCpt Y S x)
    (τ : CMType H) : Function.Injective (inO A τ) := by
  classical
  unfold inO
  rw [LinearMap.coe_comp]
  refine LinearMap.inr_injective.comp ?_
  rw [LinearMap.coe_single]
  exact Pi.single_injective τ

theorem cc_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐), ∀ s, LinearIndependent Ω (cc 𝔐 bW bO s) ∧ Submodule.span Ω (Set.range (cc 𝔐 bW bO s)) = VV 𝔐 s := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO s
  rcases s with τ | τ
  · have h := basis_image (bW τ) ((inW 𝔐).comp (𝔐.Vgen (.inl τ)).subtype)
      ((inW_injective 𝔐).comp Subtype.val_injective)
    rw [Submodule.map_comp, Submodule.map_subtype_top] at h
    exact h
  · exact basis_image (bO τ) (inO 𝔐 τ) (inO_injective 𝔐 τ)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDegreeFormula
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

theorem flag_total_normal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → (∀ q : Z, genPt ξ' ⤳ q) → GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) → Smooth f → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ _ Z ξ' f _ _ _ hf
  exact GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f 𝔐.normal

end GlobalTheory.CompanionTheory.Ar.PB.FMX
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IteratedDerivBoundGaussianGrowthStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterated_deriv_bound_gaussian_growth : ∀ (f : ℂ → ℂ) (M lam : ℝ) (n n' i : ℕ), Differentiable ℂ f → 0 < lam → 1 ≤ n → 1 ≤ n' → i ≤ n' → (∀ τ, ‖f τ‖ ≤ M * Real.exp (n * ‖τ‖ ^ 2 * lam ^ 2 / 2)) → ‖iteratedDeriv i f 0‖ ≤ Real.sqrt (Real.exp 1 * n * n') ^ i * lam ^ i * M := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.norm_iteratedDeriv_zero_le_of_gaussian_growth | exact GlobalTheory.CompanionTheory.Ar.Sl.norm_iteratedDeriv_zero_le_of_gaussian_growth | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.norm_iteratedDeriv_zero_le_of_gaussian_growth <;> assumption)
end

