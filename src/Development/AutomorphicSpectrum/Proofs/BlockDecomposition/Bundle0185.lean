module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0161
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0164
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0174
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorLiftKernelModPrime
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.TensOne

open TensorProduct

section Generic

variable {R S W C : Type} [CommRing R] [CommRing S] [CommRing W] [CommRing C]
  [Algebra R S] [Algebra R W] [Algebra R C]

theorem tmul_mul_natCast_mem (p : ℕ) (e : S) (x : W) :
    (e * (p : S)) ⊗ₜ[R] x ∈ Ideal.span {(p : S ⊗[R] W)} := by
  have hp : (p : S ⊗[R] W) = (p : S) ⊗ₜ[R] (1 : W) :=
    (map_natCast (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] W) p).symm
  have : (e * (p : S)) ⊗ₜ[R] x = (p : S ⊗[R] W) * (e ⊗ₜ[R] x) := by
    rw [hp, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem tmul_natCast_mul_mem (p : ℕ) (e : S) (x : W) :
    e ⊗ₜ[R] (x * (p : W)) ∈ Ideal.span {(p : S ⊗[R] W)} := by
  have hp : (p : S ⊗[R] W) = (1 : S) ⊗ₜ[R] (p : W) :=
    (map_natCast (Algebra.TensorProduct.includeRight : W →ₐ[R] S ⊗[R] W).toRingHom p).symm
  have : e ⊗ₜ[R] (x * (p : W)) = (p : S ⊗[R] W) * (e ⊗ₜ[R] x) := by
    rw [hp, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm x]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def gsum (d : ℕ → S) (w : ℕ →₀ W) : S ⊗[R] W := w.sum fun k x => d k ⊗ₜ[R] x

theorem gsum_add (d : ℕ → S) (w w' : ℕ →₀ W) :
    (gsum d (w + w') : S ⊗[R] W) = gsum d w + gsum d w' :=
  Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _) fun _ _ _ => TensorProduct.tmul_add _ _ _

theorem exists_gsum (p : ℕ) (d : ℕ → S)
    (hsurj : ∀ a : S, ∃ (s : Finset ℕ) (c : ℕ → R), a - ∑ k ∈ s, algebraMap R S (c k) * d k ∈ Ideal.span {(p : S)})
    (z : S ⊗[R] W) : ∃ w : ℕ →₀ W, z - gsum d w ∈ Ideal.span {(p : S ⊗[R] W)} := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    obtain ⟨s, c, hc⟩ := hsurj a
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hc
    refine ⟨∑ k ∈ s, Finsupp.single k (c k • x), ?_⟩
    have h1 : (gsum d (∑ k ∈ s, Finsupp.single k (c k • x)) : S ⊗[R] W) =
        (∑ k ∈ s, algebraMap R S (c k) * d k) ⊗ₜ[R] x := by
      rw [gsum, ← Finsupp.sum_finsetSum_index (fun _ => TensorProduct.tmul_zero _ _)
        (fun _ _ _ => TensorProduct.tmul_add _ _ _), TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finsupp.sum_single_index (h := fun k x => d k ⊗ₜ[R] x) (TensorProduct.tmul_zero _ _), ← Algebra.smul_def,
        TensorProduct.smul_tmul]
    rw [h1, ← TensorProduct.sub_tmul, ← he]
    exact tmul_mul_natCast_mem p e x
  | add x y hx hy =>
    obtain ⟨w, hw⟩ := hx
    obtain ⟨w', hw'⟩ := hy
    refine ⟨w + w', ?_⟩
    have : x + y - gsum d (w + w') = (x - gsum d w) + (y - gsum d w') := by
      rw [gsum_add]; ring
    rw [this]
    exact add_mem hw hw'

theorem generic (p : ℕ) (d : ℕ → S) (r0 : R) (f : S →ₐ[R] C) (g : W →ₐ[R] C)
    (hsurj : ∀ a : S, ∃ (s : Finset ℕ) (c : ℕ → R), a - ∑ k ∈ s, algebraMap R S (c k) * d k ∈ Ideal.span {(p : S)})
    (hv : ∀ k, algebraMap R S r0 * d k ∈ Ideal.span {(p : S)})
    (hK : ∀ (s : Finset ℕ) (w : ℕ → W), ∑ k ∈ s, f (d k) * g (w k) = 0 →
      ∀ k ∈ s, w k ∈ Ideal.span {algebraMap R W r0, (p : W)})
    (hC : (p : C) = 0) (z : S ⊗[R] W)
    (hz : Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) z = 0) :
    z ∈ Ideal.span {(p : S ⊗[R] W)} := by
  obtain ⟨w, hw⟩ := exists_gsum p d hsurj z
  have hL : Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) (z - gsum d w) = 0 := by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hw
    rw [← hy, map_mul, map_natCast, hC, mul_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, hz, zero_sub, neg_eq_zero, gsum, Finsupp.sum, map_sum] at hL
  have hsum : ∑ k ∈ w.support, f (d k) * g (w k) = 0 := by
    rw [← hL]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.TensorProduct.lift_tmul]
  have hk := hK _ _ hsum
  have hG : (gsum d w : S ⊗[R] W) ∈ Ideal.span {(p : S ⊗[R] W)} := by
    refine Ideal.sum_mem _ fun k hks => ?_
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (hk k hks)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (hv k)
    have h1 : d k ⊗ₜ[R] (u * algebraMap R W r0) = (e * (p : S)) ⊗ₜ[R] u := by
      rw [he, mul_comm u, ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
    change d k ⊗ₜ[R] (w k) ∈ _
    rw [← huv, TensorProduct.tmul_add, h1]
    exact add_mem (tmul_mul_natCast_mem p e u) (tmul_natCast_mul_mem p (d k) v)
  have := add_mem hw hG
  rwa [sub_add_cancel] at this

end Generic

section Specific

variable {l : ℕ} [Fact l.Prime]

def base : PAlg l where
  A := Ob l
  s := RingHom.id _
  perf := inferInstance
  compl := GlobalTheory.CompanionTheory.TiltCompl.complete_tf.1
  tf := GlobalTheory.CompanionTheory.TiltCompl.complete_tf.2

theorem isBase_base : IsBase l (base (l := l)) := Function.bijective_id

def d (k : ℕ) : Acris l := AdicCompletion.of _ _ (ACris.dpowZero (xi0_mem (l := l)) k)

theorem cris_d (A : PAlg l) (n k : ℕ) : A.cris n (d k) = A.dxi n k := by
  rw [d, cris_of]
  refine congrArg (A.mkAcr n) (Subtype.ext ?_)
  exact awayW_dpw A.s k (ACris.isUnit_natCast (K := ℂ_[l]) (p := l) k.factorial_ne_zero) (xi0 l)

theorem sW_base (x : Ainf l) : (base (l := l)).sW x = x := wmap_id x

theorem cris_teich (a : Ob l) :
    (base (l := l)).cris 1 (algebraMap (Ainf l) (Acris l) (WittVector.teichmuller l a)) =
      (base (l := l)).aTo1 a := by
  have h1 := (base (l := l)).aTo1_coeff (WittVector.teichmuller l a)
  rw [WittVector.teichmuller_coeff_zero] at h1
  have h2 := (base (l := l)).cris_algebraMap 1 (WittVector.teichmuller l a)
  rw [sW_base] at h2
  rw [h1]
  exact h2

theorem mem_of_cris (a : Acris l) (h : (base (l := l)).cris 1 a = 0) : a ∈ Ideal.span {(l : Acris l)} := by
  have := (RingHom.mem_ker).2 h
  rwa [((_root_.GlobalTheory.CompanionTheory.BaseAcris.main base isBase_base).2 1).2, pow_one] at this

theorem hsurj (a : Acris l) : ∃ (s : Finset ℕ) (c : ℕ → Ainf l),
    a - ∑ k ∈ s, algebraMap (Ainf l) (Acris l) (c k) * d (l * k) ∈ Ideal.span {(l : Acris l)} := by
  obtain ⟨c, hc⟩ := (_root_.GlobalTheory.CompanionTheory.PerfFil.Expand.main (base (l := l))).1 ((base (l := l)).cris 1 a)
  refine ⟨c.support, fun k => WittVector.teichmuller l (c k), mem_of_cris _ ?_⟩
  have e : (base (l := l)).expand c =
      ∑ k ∈ c.support, (base (l := l)).aTo1 (c k) * (base (l := l)).dxi 1 (l * k) := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, ← hc, e, sub_eq_zero, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, cris_teich, cris_d]

def r0 : Ainf l := WittVector.teichmuller l (pFlat l ^ l)

theorem hv (k : ℕ) : algebraMap (Ainf l) (Acris l) (r0 (l := l)) * d k ∈ Ideal.span {(l : Acris l)} := by
  refine mem_of_cris _ ?_
  rw [map_mul, r0, cris_teich, cris_d]
  exact (_root_.GlobalTheory.CompanionTheory.PerfFil.Expand.main (base (l := l))).2.2.2 k

theorem hK (A : PAlg l) (s : Finset ℕ) (w : ℕ → A.W)
    (h : ∑ k ∈ s, A.cris 1 (d (l * k)) * A.toAcr 1 (w k) = 0) (k : ℕ) (hks : k ∈ s) :
    w k ∈ Ideal.span {algebraMap (Ainf l) A.W r0, (l : A.W)} := by
  have hexp : A.expand (Finsupp.indicator s fun k _ => (w k).coeff 0) = 0 := by
    rw [expand, Finsupp.sum_of_support_subset _ (Finsupp.support_indicator_subset _ _) _ (by simp), ← h]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finsupp.indicator_of_mem hk, aTo1_coeff, cris_d, mul_comm]
  have hk := (_root_.GlobalTheory.CompanionTheory.ExpandKer.expand_eq_zero_iff A _).1 hexp k
  rw [Finsupp.indicator_of_mem hks] at hk
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hk
  have hr : algebraMap (Ainf l) A.W r0 = WittVector.teichmuller l (A.pi ^ l) := by
    change A.sW _ = _
    rw [r0, sW, WittVector.map_teichmuller, map_pow]
    rfl
  have hz : (w k - WittVector.teichmuller l b * algebraMap (Ainf l) A.W r0).coeff 0 = 0 := by
    rw [← WittVector.constantCoeff_apply, map_sub, map_mul, hr]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [hb, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff _).2 hz)
  exact Ideal.mem_span_pair.2 ⟨WittVector.teichmuller l b, t, by rw [ht]; ring⟩

theorem natCast_acr (A : PAlg l) : (l : A.Acr 1) = 0 := by
  have := A.pow_l_acr 1
  rwa [pow_one] at this

theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (z : TensorProduct (Ainf l) (Acris l) A.W),
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr 1))
      (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr 1)) (fun _ _ => Commute.all _ _) z = 0 →
    z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W)} := by
  intro l _ A z hz
  exact generic (R := Ainf l) (S := Acris l) (W := A.W) (C := A.Acr 1) l (fun k => d (l * k)) r0
    (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr 1)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr 1))
    hsurj (fun k => hv _) (fun s w h k hk => hK A s w h k hk) (natCast_acr A) z hz

end Specific

end GlobalTheory.CompanionTheory.TensOne
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionSphericalK
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing Pointwise
open PositivityTheory.RgEis PositivityTheory.RgEis.MG GroundTheory.Global GroundTheory.Automorphic

namespace GlobalTheory.CompanionTheory.EisTestK

theorem nhd_choice {K K₀ : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [Group K₀] [TopologicalSpace K₀] [IsTopologicalGroup K₀] [CompactSpace K₀] [T2Space K₀]
    (j : K →* K₀) (hj : Continuous j) (S : Subgroup K₀) (hS : IsClosed (S : Set K₀))
    (N₁ : Set K₀) (hN : N₁ ∈ 𝓝 (1 : K₀)) (V : Set K) (hV : V ∈ 𝓝 (1 : K)) :
    ∃ U ∈ 𝓝 (1 : K₀), ∀ (κ : K) (p u : K₀), p ∈ S → u ∈ U → j κ = p * u →
      ∃ r v : K, j r ∈ S ∧ v ∈ V ∧ κ = r * v ∧ ∀ u' ∈ U, j v * u'⁻¹ ∈ N₁ := by
  have hcont : Tendsto (fun x : K₀ × K₀ => x.1 * x.2⁻¹) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1) := by
    have h : Continuous (fun x : K₀ × K₀ => x.1 * x.2⁻¹) := by fun_prop
    have := h.tendsto ((1 : K₀), (1 : K₀))
    simpa [nhds_prod_eq] using this
  obtain ⟨W, hW, hWN⟩ := Filter.mem_prod_self_iff.1 (hcont hN)
  have hjW : j ⁻¹' W ∈ 𝓝 (1 : K) := hj.continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨V₀, hV₀sub, hV₀o, h1⟩ := mem_nhds_iff.1 (Filter.inter_mem hV hjW)
  let Q : Subgroup K := S.comap j
  let A : Set K := (Q : Set K) * V₀
  have hAo : IsOpen A := hV₀o.mul_left
  have hC : IsCompact (j '' Aᶜ) := (hAo.isClosed_compl.isCompact).image hj
  have hScpt : IsCompact (S : Set K₀) := hS.isCompact
  let T : Set K₀ := (S : Set K₀) * (j '' Aᶜ)
  have hT : IsCompact T := hScpt.mul hC
  have h1T : (1 : K₀) ∉ T := by
    rintro ⟨p, hp, c, ⟨x, hx, rfl⟩, hpc⟩
    apply hx
    have hjx : j x ∈ S := by
      have : j x = p⁻¹ := eq_inv_of_mul_eq_one_right hpc
      rw [this]; exact S.inv_mem hp
    exact ⟨x, hjx, 1, h1, by simp⟩
  refine ⟨W ∩ Tᶜ, Filter.inter_mem hW (hT.isClosed.isOpen_compl.mem_nhds h1T), ?_⟩
  intro κ p u hp hu hκ
  by_cases hκA : κ ∈ A
  · obtain ⟨r, hr, v, hv, rfl⟩ := hκA
    refine ⟨r, v, hr, (hV₀sub hv).1, rfl, fun u' hu' => ?_⟩
    exact hWN (Set.mk_mem_prod (hV₀sub hv).2 hu'.1)
  · exfalso
    apply hu.2
    refine ⟨p⁻¹, S.inv_mem hp, j κ, ⟨κ, hκA, rfl⟩, ?_⟩
    simp [hκ]

section Concrete

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G]

theorem dgl_mem_stab (d : ι → IdeleGroup k) (i : ι) : dgl d ∈ stab 𝔸[k] ({i} : Set ι) := by
  intro r hr c hc
  have hrc : r ≠ c := fun h => hr (h ▸ hc)
  exact ⟨Matrix.diagonal_apply_ne _ hrc, Matrix.diagonal_apply_ne _ hrc⟩

theorem kap_mem_stab_iff (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) (g : G) :
    kap π d g ∈ stab 𝔸[k] ({i} : Set ι) ↔ π g ∈ stab 𝔸[k] ({i} : Set ι) := by
  have hD := dgl_mem_stab d i
  constructor
  · intro h
    have e : π g = dgl d * kap π d g * (dgl d)⁻¹ := by simp [kap, mul_assoc]
    rw [e]
    exact mul_mem (mul_mem hD h) (inv_mem hD)
  · intro h
    exact mul_mem (mul_mem (inv_mem hD) h) hD

theorem bdet_congr {R : Type} [CommRing R] {s : Set ι} {g g' : GL ι R}
    (h : (g : Matrix ι ι R).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) =
      (g' : Matrix ι ι R).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)) : bdet s g = bdet s g' := by
  unfold bdet
  split_ifs with h1 h2 h2
  · exact Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h])
  · exact absurd (by rwa [h] at h1) h2
  · exact absurd (by rwa [← h] at h2) h1
  · rfl

theorem bdet_kap (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) (g : G) :
    bdet ({i} : Set ι) (kap π d g) = bdet ({i} : Set ι) (π g) := by
  apply bdet_congr
  ext ⟨a, ha⟩ ⟨b, hb⟩
  obtain rfl : a = i := ha
  obtain rfl : b = a := hb
  have e : (((dgl d)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) =
      Matrix.diagonal fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]) := rfl
  have e' : ((dgl d : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) = Matrix.diagonal fun i => (d i : 𝔸[k]) := rfl
  simp only [Matrix.submatrix_apply, kap, Units.val_mul, e, e', Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [mul_right_comm, Units.inv_mul, one_mul]

end Concrete

theorem testK : StdGood → BdetLaw → TestFun → TestK := by
  intro hStd hB hT G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hSide V hV
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : CompactSpace ((adStd k).kGL ι) := isCompact_iff_compactSpace.1 ((hStd k).kcpt ι)
  obtain ⟨hcl, hmul, hcb, -, -, -⟩ := hB k 𝔸[k] (adStd k) (hStd k) ι ({i} : Set ι)
  let j : K →* (adStd k).kGL ι :=
    { toFun := fun κ => ⟨kap π d κ, hSide.piK κ κ.2⟩
      map_one' := by apply Subtype.ext; simp [kap]
      map_mul' := fun a b => by apply Subtype.ext; simp [kap, mul_assoc] }
  have hj : Continuous j := by
    refine Continuous.subtype_mk ?_ _
    unfold kap
    exact (continuous_const.mul (hSide.cont.comp continuous_subtype_val)).mul continuous_const
  let S : Subgroup ((adStd k).kGL ι) := (stab 𝔸[k] ({i} : Set ι)).comap ((adStd k).kGL ι).subtype
  have hS : IsClosed (S : Set ((adStd k).kGL ι)) := hcl.preimage continuous_subtype_val
  have hb1 : bdet ({i} : Set ι) (1 : GL ι 𝔸[k]) = 1 := by
    have := hmul 1 (one_mem _) 1 (one_mem _)
    simpa using this
  let f : (adStd k).kGL ι → ℂ := fun p => (ω.toIdele (bdet ({i} : Set ι) p.1) : ℂ)
  have hf1 : f 1 = 1 := by
    show (ω.toIdele (bdet ({i} : Set ι) (1 : GL ι 𝔸[k])) : ℂ) = 1
    rw [hb1]
    simp [HeckeCharacter.toIdele_apply]
  have hfc : ContinuousOn f (S : Set ((adStd k).kGL ι)) := by
    have h1 : ContinuousOn (fun p : (adStd k).kGL ι => bdet ({i} : Set ι) p.1) (S : Set ((adStd k).kGL ι)) :=
      hcb.comp continuous_subtype_val.continuousOn fun p hp => hp
    exact continuous_subtype_val.comp_continuousOn (ω.continuous_toIdele.comp_continuousOn h1)
  obtain ⟨N₁, hN₁, hNf⟩ : ∃ N₁ ∈ 𝓝 (1 : (adStd k).kGL ι), ∀ p ∈ S, p ∈ N₁ → ‖f p - 1‖ ≤ 1 / 4 := by
    have h := hfc 1 (one_mem S)
    have hm : f ⁻¹' Metric.closedBall 1 (1 / 4) ∈ 𝓝[(S : Set ((adStd k).kGL ι))] (1 : (adStd k).kGL ι) :=
      h (by rw [hf1]; exact Metric.closedBall_mem_nhds _ (by norm_num))
    obtain ⟨u, huo, hu1, hus⟩ := mem_nhdsWithin.1 hm
    refine ⟨u, huo.mem_nhds hu1, fun p hp hpu => ?_⟩
    have := hus ⟨hpu, hp⟩
    simpa [dist_eq_norm] using this
  obtain ⟨U, hU, hUmain⟩ := nhd_choice j hj S hS N₁ hN₁ V hV
  obtain ⟨Ψ, Ψ₁, ψ, hΨ, hΨ₁, hψc, hψ1, hfac, hsupp, hlaw, hz, hone⟩ := hT k ι i ω hSide.sq U hU
  refine ⟨Ψ, Ψ₁, ψ ∘ j, hΨ, hΨ₁, hψc.comp hj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hψ1
  · intro r κ hr
    have hrS : (j r).1 ∈ stab 𝔸[k] ({i} : Set ι) := (kap_mem_stab_iff π d i r).2 ((hSide.mem _).1 hr)
    show ψ (j (r * κ)) = c r * ψ (j κ)
    rw [map_mul, hlaw _ _ hrS, (hSide.val _ hr).1]
    rw [show (j r).1 = kap π d r from rfl, bdet_kap]
  · intro κ hκ
    obtain ⟨p, hp, u, hu, hκe, -⟩ := hsupp (j κ) hκ
    obtain ⟨r, v, hr, hv, rfl, hvN⟩ := hUmain κ p u hp hu hκe
    have hrS : (j r).1 ∈ stab 𝔸[k] ({i} : Set ι) := hr
    have hrP : (r : G) ∈ P := (hSide.mem _).2 ((kap_mem_stab_iff π d i r).1 hr)
    refine ⟨r, v, hrP, hv, rfl, ?_⟩
    have hl := hlaw (j r) (j v) hrS
    have hφv : ψ (j v) ≠ 0 := fun h => hκ (by
      show ψ (j (r * v)) = 0
      rw [map_mul, hl, h, mul_zero])
    obtain ⟨p', hp', u', hu', hve, hval⟩ := hsupp (j v) hφv
    have hpN : p' ∈ N₁ := by
      have := hvN u' hu'
      rwa [hve, mul_inv_cancel_right] at this
    have hb : ‖f p' - 1‖ ≤ 1 / 4 := hNf p' hp' hpN
    show ‖ψ (j v) - (‖ψ (j v)‖ : ℂ)‖ ≤ ‖ψ (j v)‖ / 4
    generalize ψ (j v) = a at hval
    have e : a - (‖a‖ : ℂ) = (f p' - 1) * (‖a‖ : ℂ) := by
      rw [sub_mul, one_mul]
      exact congrArg (· - (‖a‖ : ℂ)) hval
    rw [e, norm_mul, Complex.norm_real, norm_norm]
    nlinarith [norm_nonneg a]
  · intro s κ
    show globalZeta (fun t => Ψ (t • vec (kap π d κ) i)) ω s = globalZeta (fun t => Ψ₁ fun _ => t) ω s * ψ (j κ)
    have hfun : (fun t => Ψ (t • vec (kap π d κ) i)) = fun t => (Ψ₁ fun _ => t) * ψ (j κ) :=
      funext fun t => hfac t (j κ)
    rw [hfun]
    unfold globalZeta
    rw [← integral_mul_const]
    congr 1
    ext x
    ring
  · obtain ⟨z, hz1, hz2⟩ := hz
    exact ⟨z, by linarith, hz2⟩
  · exact hone

end GlobalTheory.CompanionTheory.EisTestK
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegrandTensor
section
noncomputable section

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.RgEisTF

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup

theorem zetaIntegrand_tensor {k : Type} [Field k] [NumberField k]
    (φ : 𝓢(Unit → mixedSpace k, ℂ)) (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ)
    (ω : HeckeCharacter k) (s : ℂ) (x : IdeleGroup k) :
    GJMatrix.schwartzBruhatTensorPi φ g (fun _ => (x : 𝔸[k])) * (ω.toIdele x : ℂ) *
        ((ideleModule k x : ℝ) : ℂ) ^ s =
      (rd φ (fun _ => ((toInfinite k x : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k)) *
          (ω.toIdele (ofInfinite (toInfinite k x)) : ℂ) *
          ((ideleModule k (ofInfinite (toInfinite k x)) : ℝ) : ℂ) ^ s) *
        (g (fun _ => ((toFinite k x : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k)) *
          (ω.toIdele (ofFinite (toFinite k x)) : ℂ) *
          ((ideleModule k (ofFinite (toFinite k x)) : ℝ) : ℂ) ^ s) := by
  have hchi : (ω.toIdele x : ℂ) = (ω.toIdele (ofFinite (toFinite k x)) : ℂ) *
      (ω.toIdele (ofInfinite (toInfinite k x)) : ℂ) := by
    rw [← Circle.coe_mul, ← map_mul, ofFinite_mul_ofInfinite]
  have hmod : ((ideleModule k x : ℝ) : ℂ) ^ s =
      ((ideleModule k (ofInfinite (toInfinite k x)) : ℝ) : ℂ) ^ s *
        ((ideleModule k (ofFinite (toFinite k x)) : ℝ) : ℂ) ^ s := by
    have h : (ideleModule k x : ℝ) = (ideleModule k (ofInfinite (toInfinite k x)) : ℝ) *
        (ideleModule k (ofFinite (toFinite k x)) : ℝ) := by
      conv_lhs => rw [← ofFinite_mul_ofInfinite x, map_mul]
      rw [mul_comm]
      rfl
    rw [h, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (ideleModule k _).2.le
      (ideleModule k _).2.le]
  rw [hchi, hmod]
  change φ (fun _ => homeomorphMixedSpace k (x : 𝔸[k]).1) * g (fun _ => (x : 𝔸[k]).2) * _ * _ = _
  change _ = (φ (fun _ => homeomorphMixedSpace k (x : 𝔸[k]).1) * _ * _) *
    (g (fun _ => (x : 𝔸[k]).2) * _ * _)
  ring

theorem zSplit : ZSplit := by
  intro k _ _ φ g ω s _
  set A : (InfiniteAdeleRing k)ˣ → ℂ := fun a =>
    rd φ (fun _ => (a : InfiniteAdeleRing k)) * (ω.toIdele (ofInfinite a) : ℂ) *
      ((ideleModule k (ofInfinite a) : ℝ) : ℂ) ^ s with hA
  set B : (FiniteAdeleRing (𝓞 k) k)ˣ → ℂ := fun b =>
    g (fun _ => (b : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite b) : ℂ) *
      ((ideleModule k (ofFinite b) : ℝ) : ℂ) ^ s with hB
  have hF : ∀ x : IdeleGroup k,
      GJMatrix.schwartzBruhatTensorPi φ g (fun _ => (x : 𝔸[k])) * (ω.toIdele x : ℂ) *
        ((ideleModule k x : ℝ) : ℂ) ^ s = (fun p => A p.1 * B p.2) (IdeleGroup.prodEquiv k x) :=
    zetaIntegrand_tensor φ g ω s
  have hemb : MeasurableEmbedding (IdeleGroup.prodEquiv k) :=
    (IdeleGroup.prodEquiv k).toHomeomorph.measurableEmbedding
  unfold globalZeta zInf zFin
  simp_rw [hF]
  rw [(measurePreserving_prodEquiv (K := k)).integral_comp hemb (fun p => A p.1 * B p.2)]
  exact integral_prod_mul A B

end GlobalTheory.CompanionTheory.RgEisTF
end
end

