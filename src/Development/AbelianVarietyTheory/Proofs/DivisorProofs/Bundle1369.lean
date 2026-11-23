module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapMemMaximalIdealIff
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.LocalTangent

open IsLocalRing

variable {k S : Type} [Field k] [CommRing S] [IsLocalRing S] [Algebra k S]

theorem algebraMap_mem_maximalIdeal_iff (c : k) :
    algebraMap k S c ∈ maximalIdeal S ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
    exact h ((isUnit_iff_ne_zero.mpr hc).map (algebraMap k S))
  · rintro rfl
    simp

theorem residue_eq {π : S → k} (hπ : ∀ s, s - algebraMap k S (π s) ∈ maximalIdeal S)
    (s : S) (c : k) (h : s - algebraMap k S c ∈ maximalIdeal S) : π s = c := by
  have hm : algebraMap k S (π s - c) ∈ maximalIdeal S := by
    have := sub_mem h (hπ s)
    rw [map_sub]; convert this using 1; ring
  rw [algebraMap_mem_maximalIdeal_iff] at hm
  exact sub_eq_zero.mp hm

def tangentHom (π : S → k) (hπ : ∀ s, s - algebraMap k S (π s) ∈ maximalIdeal S)
    (f : S →ₗ[k] k) (hf1 : f 1 = 0) (hf2 : ∀ y ∈ maximalIdeal S ^ 2, f y = 0) :
    S →ₐ[k] DualNumber k where
  toFun s := TrivSqZeroExt.inl (π s) + TrivSqZeroExt.inr (f s)
  map_one' := by
    have : π 1 = 1 := residue_eq hπ 1 1 (by simp)
    ext <;> simp [this, hf1]
  map_mul' s t := by
    have hm : π (s * t) = π s * π t := residue_eq hπ _ _ (by
      rw [map_mul]
      convert add_mem (Ideal.mul_mem_right t _ (hπ s)) (Ideal.mul_mem_left _ (algebraMap k S (π s)) (hπ t))
        using 1
      ring)
    have hfa : ∀ c, f (algebraMap k S c) = 0 := by
      intro c; rw [Algebra.algebraMap_eq_smul_one, map_smul, hf1, smul_zero]
    have e : s * t = algebraMap k S (π s * π t) + π s • (t - algebraMap k S (π t)) +
        π t • (s - algebraMap k S (π s)) +
        (s - algebraMap k S (π s)) * (t - algebraMap k S (π t)) := by
      simp only [Algebra.smul_def, map_mul]; ring
    have hf : f (s * t) = π s * f t + π t * f s := by
      have huv := hf2 _ (by rw [pow_two]; exact Ideal.mul_mem_mul (hπ s) (hπ t))
      rw [e, map_add (f := _), map_add (f := _), map_add (f := _), map_smul, map_smul, huv, map_sub, map_sub, hfa, hfa, hfa]
      simp
    ext <;> simp [hm, hf] <;> ring
  map_zero' := by
    have : π 0 = 0 := residue_eq hπ 0 0 (by simp)
    ext <;> simp [this]
  map_add' s t := by
    have : π (s + t) = π s + π t := residue_eq hπ _ _ (by
      rw [map_add (f := _)]; convert add_mem (hπ s) (hπ t) using 1; ring)
    ext <;> simp [this]
  commutes' c := by
    have : π (algebraMap k S c) = c := residue_eq hπ _ _ (by simp)
    have h0 : f (algebraMap k S c) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hf1, smul_zero]
    ext <;> simp [this, h0, TrivSqZeroExt.algebraMap_eq_inl]

theorem tangentHom_snd (π : S → k) (hπ : ∀ s, s - algebraMap k S (π s) ∈ maximalIdeal S)
    (f : S →ₗ[k] k) (hf1 : f 1 = 0) (hf2 : ∀ y ∈ maximalIdeal S ^ 2, f y = 0) (s : S) :
    (tangentHom π hπ f hf1 hf2 s).snd = f s := by
  simp [tangentHom]

theorem epsScaleR_snd (c : k) (x : DualNumber k) : (epsScaleR c x).snd = c * x.snd := by
  simp [epsScaleR]

end GlobalTheory.LocalTangent

namespace GlobalTheory.LocalTangent

open IsLocalRing

variable {k S : Type} [Field k] [CommRing S] [IsLocalRing S] [Algebra k S]

theorem exists_form {a b : S} (ha : a ∈ maximalIdeal S) (hb : b ∈ maximalIdeal S)
    (h : ∀ c : k, a - c • b ∉ maximalIdeal S ^ 2) :
    ∃ f : S →ₗ[k] k, f 1 = 0 ∧ (∀ y ∈ maximalIdeal S ^ 2, f y = 0) ∧ f b = 0 ∧ f a = 1 := by
  let P : Submodule k S := Submodule.span k {1, b} ⊔ (maximalIdeal S ^ 2).restrictScalars k
  have haP : a ∉ P := by
    intro hP
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hP
    obtain ⟨l, r, rfl⟩ := Submodule.mem_span_pair.mp hy
    have hz2 : z ∈ maximalIdeal S ^ 2 := hz
    have hz' : z ∈ maximalIdeal S := Ideal.pow_le_self two_ne_zero hz2
    have hl : l = 0 := by
      rw [← algebraMap_mem_maximalIdeal_iff (S := S)]
      have e : algebraMap k S l = a - r • b - z := by
        rw [← hyz, Algebra.algebraMap_eq_smul_one]; abel
      rw [e]
      exact sub_mem (sub_mem ha (Submodule.smul_of_tower_mem _ r hb)) hz'
    apply h r
    have e : a - r • b = z := by rw [← hyz, hl]; simp
    rw [e]; exact hz2
  obtain ⟨g, hga, hgP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem haP (by infer_instance)
  have hg0 : ∀ y ∈ P, g y = 0 := fun y hy => by
    have : g y ∈ P.map g := Submodule.mem_map_of_mem hy
    rw [hgP] at this; exact (Submodule.mem_bot k).mp this
  refine ⟨(g a)⁻¹ • g, ?_, ?_, ?_, ?_⟩
  · simp [hg0 1 (Submodule.mem_sup_left (Submodule.subset_span (by simp)))]
  · intro y hy
    simp [hg0 y (Submodule.mem_sup_right hy)]
  · simp [hg0 b (Submodule.mem_sup_left (Submodule.subset_span (by simp)))]
  · simp [hga]

theorem pair_dependent
    (h1 : ∀ a : S, ∃ c : k, a - algebraMap k S c ∈ maximalIdeal S)
    (h3 : ∀ ψ₁ ψ₂ : S →ₐ[k] DualNumber k, ∃ c : k,
      (ψ₁ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₂ : S →+* DualNumber k) ∨
      (ψ₂ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₁ : S →+* DualNumber k))
    {a b : S} (ha : a ∈ maximalIdeal S) (hb : b ∈ maximalIdeal S) :
    ∃ c : k, a - c • b ∈ maximalIdeal S ^ 2 ∨ b - c • a ∈ maximalIdeal S ^ 2 := by
  by_contra hne
  push_neg at hne
  choose π hπ using h1
  obtain ⟨f₁, h11, h12, h13, h14⟩ := exists_form ha hb (fun c => (hne c).1)
  obtain ⟨f₂, h21, h22, h23, h24⟩ := exists_form hb ha (fun c => (hne c).2)
  obtain ⟨c, hc | hc⟩ := h3 (tangentHom π hπ f₁ h11 h12) (tangentHom π hπ f₂ h21 h22)
  · have := congrArg (fun φ : S →+* DualNumber k => (φ a).snd) hc
    simp only [RingHom.coe_coe, RingHom.comp_apply, epsScaleR_snd, tangentHom_snd] at this
    rw [h14, h23, mul_zero] at this
    exact one_ne_zero this
  · have := congrArg (fun φ : S →+* DualNumber k => (φ b).snd) hc
    simp only [RingHom.coe_coe, RingHom.comp_apply, epsScaleR_snd, tangentHom_snd] at this
    rw [h24, h13, mul_zero] at this
    exact one_ne_zero this

theorem maximalIdeal_isPrincipal : ∀ (k : Type) [Field k] (S : Type) [CommRing S] [IsLocalRing S] [Algebra k S],
    (∀ a : S, ∃ c : k, a - algebraMap k S c ∈ IsLocalRing.maximalIdeal S) →
    IsNilpotent (IsLocalRing.maximalIdeal S) →
    (∀ ψ₁ ψ₂ : S →ₐ[k] DualNumber k, ∃ c : k,
      (ψ₁ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₂ : S →+* DualNumber k) ∨
      (ψ₂ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₁ : S →+* DualNumber k)) →
    (IsLocalRing.maximalIdeal S).IsPrincipal := by
  intro k _ S _ _ _ h1 hnil h3
  set m := maximalIdeal S with hm
  have hx : ∃ x ∈ m, m ≤ Ideal.span {x} ⊔ m ^ 2 := by
    by_cases hle : m ≤ m ^ 2
    · exact ⟨0, zero_mem _, le_sup_of_le_right hle⟩
    · obtain ⟨x, hxm, hx2⟩ := Set.not_subset.mp hle
      refine ⟨x, hxm, fun a ha => ?_⟩
      have key : ∃ c : k, a - c • x ∈ m ^ 2 := by
        obtain ⟨c, hc | hc⟩ := pair_dependent h1 h3 ha hxm
        · exact ⟨c, hc⟩
        · have hc0 : c ≠ 0 := by
            rintro rfl; apply hx2; simpa using hc
          refine ⟨c⁻¹, ?_⟩
          have e : a - c⁻¹ • x = (-c⁻¹) • (x - c • a) := by
            rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hc0, neg_smul, neg_smul, one_smul]; abel
          rw [e]; exact Submodule.smul_of_tower_mem _ _ hc
      obtain ⟨c, hc⟩ := key
      have e : a = c • x + (a - c • x) := by abel
      rw [e]
      refine Submodule.add_mem_sup ?_ hc
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x)
  obtain ⟨x, hxm, hle⟩ := hx
  set I := Ideal.span {x}
  have hstep : ∀ n : ℕ, m ≤ I ⊔ m ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc m ≤ I ⊔ m ^ 2 := hle
        _ = I ⊔ m * m := by rw [pow_two]
        _ ≤ I ⊔ m * (I ⊔ m ^ (n + 1)) := sup_le_sup_left (Ideal.mul_mono_right ih) _
        _ = I ⊔ (m * I ⊔ m ^ (n + 1 + 1)) := by rw [Ideal.mul_sup, ← pow_succ']
        _ ≤ I ⊔ m ^ (n + 1 + 1) := sup_le (le_sup_left) (sup_le (le_sup_of_le_left Ideal.mul_le_right) le_sup_right)
  obtain ⟨n, hn⟩ := hnil
  have hmI : m ≤ I := by
    have := hstep n
    rwa [pow_succ, hn, zero_mul, Ideal.zero_eq_bot, sup_bot_eq] at this
  have hIm : I ≤ m := (Ideal.span_singleton_le_iff_mem _).mpr hxm
  exact ⟨⟨x, le_antisymm hmI hIm⟩⟩

end GlobalTheory.LocalTangent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSlabCoveredByTranslatesOfSmallerSlab
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.SlabCover

open IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F]

theorem exists_int_approx (m : ℕ) (hm : 0 < m) (y : Af F)
    (hy : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, ∃ t : Af F, (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) ∧
      y - algebraMap F (Af F) (r : F) = (m : Af F) * t := by
  have hm' : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  set g : Af F → Af F := fun x => algebraMap F (Af F) (m : F)⁻¹ * (x - y) with hg
  have hgc : Continuous g := continuous_const.mul (continuous_id.sub continuous_const)
  set U : Set (Af F) := g ⁻¹' {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F} with hU
  have hUo : IsOpen U :=
    (RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)).preimage hgc
  have hyU : y ∈ U := by
    intro v
    simp only [hg, sub_self, mul_zero]
    exact zero_mem _
  obtain ⟨ρ, hρ⟩ := (PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange (R := 𝓞 F) (K := F)).exists_mem_open hUo ⟨y, hyU⟩
  have hmm : (m : Af F) * algebraMap F (Af F) (m : F)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap F (Af F)) m, ← map_mul, mul_inv_cancel₀ hm', map_one]
  have he : algebraMap F (Af F) ρ = y + (m : Af F) * g (algebraMap F (Af F) ρ) := by
    simp only [hg, ← mul_assoc, hmm, one_mul]; ring
  have hint : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      (algebraMap F (Af F) ρ) v ∈ v.adicCompletionIntegers F := by
    intro v
    rw [he]
    show y v + (m : v.adicCompletion F) * (g (algebraMap F (Af F) ρ)) v ∈ v.adicCompletionIntegers F
    exact add_mem (hy v) (mul_mem (natCast_mem _ m) (hρ v))
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F ρ
    (fun v => by
      have h := hint v
      rw [mem_adicCompletionIntegers] at h
      exact (valuedAdicCompletion_eq_valuation' v ρ).symm.trans_le h)
  refine ⟨r, -g (algebraMap F (Af F) ρ), fun v => ?_, ?_⟩
  · show -(g (algebraMap F (Af F) ρ)) v ∈ v.adicCompletionIntegers F
    exact neg_mem (hρ v)
  · have : ((r : 𝓞 F) : F) = ρ := hr
    rw [this]
    conv_lhs => rw [he]
    ring

theorem exists_residues (m : ℕ) (hm : 0 < m) :
    ∃ S : Finset F, S.card ≤ m ^ Module.finrank ℚ F ∧ ∀ r : 𝓞 F, ∃ ρ ∈ S, ∃ q : 𝓞 F, (r : F) - ρ = (m : F) * (q : F) := by
  set b := RingOfIntegers.basis F
  set ι := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  refine ⟨(Fintype.piFinset fun _ : ι => Finset.range m).image
    (fun c => (((∑ k, (c k : ℤ) • b k : 𝓞 F)) : F)), ?_, ?_⟩
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ,
      ← Module.finrank_eq_card_basis b, RingOfIntegers.rank]
  · intro r
    have hmz : (0 : ℤ) < m := by exact_mod_cast hm
    refine ⟨_, Finset.mem_image.2 ⟨fun k => ((b.repr r k) % m).toNat, ?_, rfl⟩,
      ∑ k, ((b.repr r k) / m) • b k, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro k
      rw [Finset.mem_range]
      have h1 := Int.emod_nonneg (b.repr r k) hmz.ne'
      have h2 := Int.emod_lt_of_pos (b.repr r k) hmz
      omega
    · have hc : ∀ k, (((b.repr r k) % m).toNat : ℤ) = (b.repr r k) % m := fun k =>
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))
      have key : r - ∑ k, (((b.repr r k) % m).toNat : ℤ) • b k = (m : 𝓞 F) * ∑ k, ((b.repr r k) / m) • b k := by
        have hr := b.sum_repr r
        set a := b.repr r
        simp only [hc, Finset.mul_sum]
        conv_lhs => rw [← hr, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        have h := Int.emod_add_mul_ediv (a k) m
        have h' : ((a k % m : ℤ) : 𝓞 F) + (m : 𝓞 F) * ((a k / m : ℤ) : 𝓞 F) = ((a k : ℤ) : 𝓞 F) := by
          exact_mod_cast congrArg (fun z : ℤ => (z : 𝓞 F)) h
        simp only [zsmul_eq_mul]
        linear_combination (-(b k)) * h'
      have := congrArg (fun x : 𝓞 F => (x : F)) key
      simpa using this

end GlobalTheory.ArchDecay.SlabCover

namespace GlobalTheory.ArchDecay.SlabCover

variable {F : Type} [Field F] [NumberField F]

theorem exists_finite_residues (m : ℕ) (hm : 0 < m) :
    ∃ S : Finset F, S.card ≤ m ^ Module.finrank ℚ F ∧ ∀ y : Af F,
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F) →
      ∃ ρ ∈ S, ∃ z : Af F, (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), z v ∈ v.adicCompletionIntegers F) ∧
        y - algebraMap F (Af F) ρ = (m : Af F) * z := by
  obtain ⟨S, hS, hres⟩ := exists_residues (F := F) m hm
  refine ⟨S, hS, fun y hy => ?_⟩
  obtain ⟨r, t, ht, hrt⟩ := exists_int_approx m hm y hy
  obtain ⟨ρ, hρS, q, hq⟩ := hres r
  refine ⟨ρ, hρS, t + algebraMap F (Af F) (q : F), fun v => ?_, ?_⟩
  · show t v + algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F q) ∈ v.adicCompletionIntegers F
    exact add_mem (ht v) (PI.UnipApproxD.IntegersDenseFiniteAdeles.int_R v q)
  · have e : algebraMap F (Af F) ρ = algebraMap F (Af F) (r : F) - (m : Af F) * algebraMap F (Af F) (q : F) := by
      rw [← map_natCast (algebraMap F (Af F)) m, ← map_mul, ← map_sub, ← hq]; ring_nf
    rw [e, mul_add, ← hrt]; ring

end GlobalTheory.ArchDecay.SlabCover

namespace GlobalTheory.ArchDecay

open GlobalTheory.ArchDecay.SlabCover

theorem slab_subset_and_cover : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ c : ℕ, ∀ m : ℕ, 0 < m →
    slab F κ m ⊆ slab F κ 1 ∧ ∃ R : Finset (κ → AF F), R.card ≤ m ^ c ∧ (∀ r ∈ R, arch F r = 0) ∧
      ∀ w ∈ slab F κ 1, ∃ r ∈ R, w - r ∈ slab F κ m := by
  intro F _ _ κ _
  refine ⟨Module.finrank ℚ F * Fintype.card κ, fun m hm => ⟨?_, ?_⟩⟩
  · intro w hw i
    obtain ⟨a, ha0, hai, hae⟩ := hw i
    refine ⟨(m : AF F) * a, ?_, fun v => ?_, ?_⟩
    · show InfiniteAdeleRing.ringEquiv_mixedSpace F ((m : Ainf F) * a.1) = 0
      have : InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 = 0 := ha0
      rw [map_mul, this, mul_zero]
    · show ((m : AF F) * a).2 v ∈ v.adicCompletionIntegers F
      show (m : v.adicCompletion F) * a.2 v ∈ v.adicCompletionIntegers F
      exact mul_mem (natCast_mem _ m) (hai v)
    · rw [hae, Nat.cast_one, one_mul]
  · obtain ⟨S, hS, hres⟩ := exists_finite_residues (F := F) m hm
    let emb : (κ → F) → (κ → AF F) := fun f i => pairA F 0 (algebraMap F (Af F) (f i))
    refine ⟨(Fintype.piFinset fun _ : κ => S).image emb, ?_, ?_, ?_⟩
    · refine Finset.card_image_le.trans ?_
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, pow_mul]
      exact Nat.pow_le_pow_left hS _
    · intro r hr
      obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hr
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    · intro w hw
      have hw' := hw
      choose a ha0 hai hae using hw'
      have hy : ∀ i, ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (a i).2 v ∈ v.adicCompletionIntegers F :=
        fun i v => hai i v
      choose ρ hρS z hz hρz using fun i => hres (a i).2 (hy i)
      refine ⟨emb ρ, Finset.mem_image.2 ⟨ρ, Fintype.mem_piFinset.2 hρS, rfl⟩, ?_⟩
      have harch : arch F (emb ρ) = 0 := by
        funext i
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _
      have hout : archOut F κ (w - emb ρ) = archOut F κ w := by
        rw [map_sub, archOut_apply F κ (emb ρ), harch, map_zero, sub_zero]
      intro i
      refine ⟨pairA F 0 (z i), map_zero _, fun v => hz i v, ?_⟩
      have h1 : (a i).1 = 0 := by
        have : InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1 = 0 := ha0 i
        exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 this
      have h2 : (w - archIn F κ (archOut F κ w)) i = a i := by rw [hae i, Nat.cast_one, one_mul]
      rw [hout]
      have h3 : (w - emb ρ - archIn F κ (archOut F κ w)) i = (w - archIn F κ (archOut F κ w)) i - emb ρ i := by
        simp only [Pi.sub_apply]; abel
      rw [h3, h2]
      refine Prod.ext ?_ ?_
      · show (a i).1 - 0 = (m : Ainf F) * 0
        rw [h1, sub_zero, mul_zero]
      · show (a i).2 - algebraMap F (Af F) (ρ i) = (m : Af F) * z i
        exact hρz i

end GlobalTheory.ArchDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTraceSymplecticFormOrthonormalFrames
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.SympFrames

def sgn {p q : ℕ} : Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

theorem jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal (sgn (p := p) (q := q)) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply, sgn] <;> split_ifs <;> simp

theorem lineSign_eq {p q r s : ℕ} (x : Ix p q) (y : Ix r s) : lineSign x y = sgn x * sgn y := by
  rcases x with x | x <;> rcases y with y | y <;> simp [lineSign, sgn]

theorem trace_jm {p q r s : ℕ} (c c' : Matrix (Ix p q) (Ix r s) ℂ) :
    (cᵀ * Jm p q * c'.map star * (Jm r s)ᵀ).trace = ∑ x, ∑ y, lineSign x y * c x y * star (c' x y) := by
  rw [jm_eq_diagonal, jm_eq_diagonal, Matrix.diagonal_transpose, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, lineSign_eq, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem quad_eq_trace {α β : Type} [Fintype α] [Fintype β]
    (U U' : Matrix α β ℂ) (X : Matrix α α ℂ) (Y : Matrix β β ℂ) :
    ∑ i, ∑ j, ∑ k, ∑ l, U i j * X i k * Y j l * star (U' k l) = (Uᵀ * X * U'.map star * Yᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem frame_trace {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : ℕ}
    (X : Matrix α α ℂ) (Y : Matrix β β ℂ) (a b : ℂ) (A : Matrix α (Ix P Q) ℂ) (C : Matrix β (Ix R S) ℂ)
    (hA : Aᵀ * (a • X) * A.map star = Jm P Q) (hC : Cᵀ * (b • Y) * C.map star = Jm R S)
    (c c' : Matrix (Ix P Q) (Ix R S) ℂ) :
    a * b * ((A * c * Cᵀ)ᵀ * X * (A * c' * Cᵀ).map star * Yᵀ).trace =
      ∑ x, ∑ y, lineSign x y * c x y * star (c' x y) := by
  rw [← trace_jm, ← hA, ← hC]
  have hm : (A * c' * Cᵀ).map star = A.map star * c'.map star * (C.map star)ᵀ := by
    rw [show (star : ℂ → ℂ) = starRingEnd ℂ from rfl, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rw [hm, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm C]
  simp only [Matrix.mul_assoc]
  ring

theorem symp_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∀ (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c c' : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u → At (evI F) u' →
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → (∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) →
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := by
  intro F E _ _ _ _ _ σ α β _ _ _ _ P Q R S τ JA JB a b A C hCM hF u u' c c' _ _ hu hu'
  have key : ∀ w, a * b * piInf (τ w) (hTens (cA σ) JA JB u u') =
      ∑ x, ∑ y, lineSign x y * c w x y * star (c' w x y) := by
    intro w
    have e : piInf (τ w) (hTens (cA σ) JA JB u u') = ∑ i, ∑ j, ∑ k, ∑ l, u.map (piInf (τ w)) i j *
        JA.map (piInf (τ w)) i k * JB.map (piInf (τ w)) j l * star (u'.map (piInf (τ w)) k l) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hTens, map_sum, map_mul, GlobalTheory.WrongSignPair.piInf_cA hCM, Matrix.map_apply]
    rw [e, hu w, hu' w, quad_eq_trace]
    exact frame_trace _ _ a b (A w) (C w) (hF.2.1 w).1 (hF.2.2 w).1 (c w) (c' w)
  rw [symp, GlobalTheory.WrongSignPair.trace_evI_trace hCM τ, Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 := key w
  rw [hF.1] at h2
  rw [← h2, map_mul, map_neg, map_one]
  simp only [Complex.neg_re, Complex.mul_im, Complex.I_re, Complex.I_im, neg_one_mul, zero_mul, one_mul, zero_add]
  ring

end GlobalTheory.SympFrames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAugmentationSubspaceQuotientActionTopStatement
section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterAugmentationSubspace_quotientAction_top : ∀ {k O C Idx W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O] [Fintype Idx] [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : Idx → C →+* k), Function.Injective χ → jSub τ χ ⊤ = ⊥ → finrank k (homO σW τ) = ∑ i, finrank k (homO σW (qAct τ (mSub τ (χ i) ⊤) (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) := by
  first | (exact @GlobalTheory.HTRho.finrank_homO_eq_sum_quot) | (exact GlobalTheory.HTRho.finrank_homO_eq_sum_quot) | (intros; apply GlobalTheory.HTRho.finrank_homO_eq_sum_quot  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKsSubMapClsEqHomOStatement
section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_ksSub_map_cls_eq_finrank_homO : ∀ {k O H : Type*} [Field k] [AddCommGroup H] [Module k H] [FiniteDimensional k H] [Ring O] (σ : O →+* Module.End k H) (G Z : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z), Z ≤ G → finrank k ((ksSub σ 0 G Z).map (cls G)) = finrank k (homO (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)) (qAct σ G hG)) := by
  first | exact @GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO | exact GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO | (intros; apply GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO <;> assumption)
end

