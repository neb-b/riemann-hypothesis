module

public import Mathlib
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.CharZeroFreeModule
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlgClosedTensorIsDomain
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isDomain_tensor_of_algebraically_closed_constants :
    ∀ (K Ω C : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Field C] [Algebra K C],
      (∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) → IsDomain (Ω ⊗[K] C) :=
  @PositivityTheory.Xgn.tensor_algebraically_closed_domain

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BundleDegreeEqSumValuations
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.DegFormula

theorem finite_det {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
    {L : C.I → AddSubgroup V} (b₀ : Module.Basis (Fin (Module.finrank K V)) K V)
    (b : C.I → Module.Basis (Fin (Module.finrank K V)) K V) (hL : IsBun C L)
    (h : ∀ i, IsLatOf C i (b i) (L i)) : {i | C.v i (b₀.det (b i)) ≠ 1}.Finite := by
  obtain ⟨c, hc⟩ := hL.2
  refine (hc.union (C.fin _ (b₀.isUnit_det c).ne_zero)).subset fun i hi => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  refine hi ?_
  rw [← Module.Basis.det_mul_det _ c, map_mul, Inhab.v_det C hn.1 (h i), hn.2, mul_one]

theorem deg_formula : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (n : ℕ)
    (b₀ : Module.Basis (Fin n) K V) (b : C.I → Module.Basis (Fin n) K V), IsBun C L →
    (∀ i, IsLatOf C i (b i) (L i)) → {i | C.v i (b₀.det (b i)) ≠ 1}.Finite ∧
      deg C L = ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (b₀.det (b i))) := by
  intro K _ C V _ _ _ L n b₀ b hL h
  have hn : n = Module.finrank K V := by
    simpa using (Module.finrank_eq_card_basis b₀).symm
  subst hn
  have hf := finite_det C b₀ b hL h
  refine ⟨hf, ?_⟩
  rw [Inhab.deg_eq C b h]
  have hx : (Module.finBasis K V).det b₀ ≠ 0 := ((Module.finBasis K V).isUnit_det b₀).ne_zero
  have key : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i))) =
      (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det b₀)) +
        (C.w i : ℤ) * WithZero.log (C.v i (b₀.det (b i))) := by
    intro i
    rw [← Module.Basis.det_mul_det _ b₀, map_mul,
      WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx)
        ((Valuation.ne_zero_iff _).2 (b₀.isUnit_det (b i)).ne_zero), mul_add]
  simp only [key]
  rw [finsum_add_distrib ((C.fin _ hx).subset fun i hi h1 => hi (by simp [h1]))
    (hf.subset fun i hi h1 => hi (by simp [h1])), C.prod _ hx, zero_add]

end GlobalTheory.CompanionTheory.Ar.Crv.DegFormula
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacteristicPolynomialFreeGenerators
section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem charpoly_condition_gives_free_char_zero : ∀ (E : Type) [Field E] [NumberField E] (k W : Type) [Field k] [CharZero k] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (r : ℕ) (ρ : 𝓞 E →+* Module.End k W), (∀ a : 𝓞 E, (ρ a).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ r) → ∃ x : Fin r → W, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ :=
  PositivityTheory.Xgn.char_zero_free_module

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeInvariantLinearEquiv
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv

open GlobalTheory.CompanionTheory.Ar.Crv

variable {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
  {V' : Type} [AddCommGroup V'] [Module K V']

def tr (e : V ≃ₗ[K] V') (b : Module.Basis (Fin (Module.finrank K V)) K V) :
    Module.Basis (Fin (Module.finrank K V')) K V' :=
  (b.map e).reindex (finCongr e.finrank_eq)

theorem isLatOf_tr (e : V ≃ₗ[K] V') {i : C.I} {b : Module.Basis (Fin (Module.finrank K V)) K V}
    {L : AddSubgroup V} {L' : AddSubgroup V'} (hb : IsLatOf C i b L)
    (h : ∀ x, x ∈ L ↔ e x ∈ L') : IsLatOf C i (tr e b) L' := by
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [← h, hb]
  simp only [tr, Module.Basis.repr_reindex_apply, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  exact ⟨fun H q => H _, fun H q => by simpa using H (finCongr e.finrank_eq q)⟩

theorem det_tr (e : V ≃ₗ[K] V') (a b : Module.Basis (Fin (Module.finrank K V)) K V) :
    (tr e a).det (tr e b) = a.det b := by
  unfold tr
  rw [Module.Basis.coe_reindex, Module.Basis.det_reindex, Module.Basis.det_map]
  congr 1
  funext i
  simp

theorem deg_equiv : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (e : V ≃ₗ[K] V'),
    IsBun C L → (∀ i x, x ∈ L i ↔ e x ∈ L' i) → IsBun C L' ∧ deg C L' = deg C L := by
  intro K _ C V _ _ _ V' _ _ _ L L' e ⟨hl, b0, hb0⟩ h
  choose b hb using hl
  have hb' : ∀ i, IsLatOf C i (tr e (b i)) (L' i) := fun i => isLatOf_tr C e (hb i) (h i)
  refine ⟨⟨fun i => ⟨_, hb' i⟩, tr e b0,
    hb0.subset fun i hi hc => hi (isLatOf_tr C e hc (h i))⟩, ?_⟩
  rw [Inhab.deg_eq C _ hb', Inhab.deg_eq C _ hb]
  set c := (Module.finBasis K V').det (tr e (Module.finBasis K V)) with hc
  have hc0 : c ≠ 0 := ((Module.finBasis K V').isUnit_det _).ne_zero
  have hd0 : ∀ i, (Module.finBasis K V).det (b i) ≠ 0 := fun i =>
    ((Module.finBasis K V).isUnit_det _).ne_zero
  have h1 : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V').det (tr e (b i)))) =
      (C.w i : ℤ) * WithZero.log (C.v i c) +
        (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i))) := by
    intro i
    rw [← Module.Basis.det_mul_det _ (tr e (Module.finBasis K V)), det_tr, ← hc, map_mul,
      WithZero.log_mul ((Valuation.ne_zero_iff _).2 hc0) ((Valuation.ne_zero_iff _).2 (hd0 i)),
      mul_add]
  simp only [h1]
  rw [finsum_add_distrib, C.prod c hc0, zero_add]
  · exact (C.fin c hc0).subset fun i hi h1 => hi (by simp [h1])
  · refine (hb0.union (C.fin _ ((Module.finBasis K V).isUnit_det b0).ne_zero)).subset
      fun i hi => ?_
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
    apply hi
    show (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i))) = 0
    rw [← Module.Basis.det_mul_det _ b0, map_mul, hn.2, Inhab.v_det C hn.1 (hb i)]
    simp

end GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenProjectorsSplitAction
section
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Crv.SplitProj

open GlobalTheory.CompanionTheory.Ar.Crv

theorem exists_sum_tmul {O k : Type} [CommRing O] [Field k] (z : TensorProduct ℤ k O) :
    ∃ (m : ℕ) (c : Fin m → k) (a : Fin m → O), z = ∑ j, c j ⊗ₜ[ℤ] a j := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul c a => exact ⟨1, fun _ => c, fun _ => a, by simp⟩
  | add x y hx hy =>
    obtain ⟨m, c, a, rfl⟩ := hx
    obtain ⟨n, d, b, rfl⟩ := hy
    refine ⟨m + n, Fin.append c d, Fin.append a b, ?_⟩
    simp [Fin.sum_univ_add]

def splitMap {O k S : Type} [CommRing O] [Field k] (χ : S → (O →+* k)) :
    TensorProduct ℤ k O →ₐ[k] (S → k) :=
  Algebra.TensorProduct.lift (Algebra.ofId k (S → k))
    (Pi.algHom ℤ (fun _ : S => k) fun s => (χ s).toIntAlgHom) (fun _ _ => Commute.all _ _)

theorem splitMap_tmul {O k S : Type} [CommRing O] [Field k] (χ : S → (O →+* k)) (c : k) (a : O)
    (t : S) : splitMap χ (c ⊗ₜ[ℤ] a) t = c * χ t a := by
  simp [splitMap, Algebra.ofId_apply]

def actMap {K V O k : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] [Field k]
    [Algebra k K] (ρ : O →+* Module.End K V) : TensorProduct ℤ k O →ₐ[ℤ] Module.End K V :=
  Algebra.TensorProduct.lift
    ((algebraMap K (Module.End K V)).comp (algebraMap k K)).toIntAlgHom ρ.toIntAlgHom
    (fun c a => show Commute (algebraMap K (Module.End K V) (algebraMap k K c)) (ρ a) from
      Algebra.commute_algebraMap_left _ _)

theorem actMap_tmul {K V O k : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] [Field k]
    [Algebra k K] (ρ : O →+* Module.End K V) (c : k) (a : O) :
    actMap ρ (c ⊗ₜ[ℤ] a) = algebraMap k K c • ρ a := by
  rw [Algebra.smul_def]
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem smul_mem_of_isBun {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V]
    [Module K V] {L : C.I → AddSubgroup V} (hL : IsBun C L) (i : C.I) {c : K}
    (hc : C.v i c ≤ 1) {x : V} (hx : x ∈ L i) : c • x ∈ L i := by
  obtain ⟨b, hb⟩ := hL.1 i
  refine (hb _).2 fun q => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_one' hc ((hb _).1 hx q)

theorem split_proj : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k]
    [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ →
    (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L →
    (∀ a, IsHom C L L (ρ a)) →
    ∃ e : S → Module.End K V, (∀ s, IsHom C L L (e s)) ∧
      (∀ s x, e s x ∈ (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a)))) ∧
      (∀ s, ∀ x ∈ (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))), e s x = x) ∧
      (∀ x, ∑ s, e s x = x) ∧
      ∀ s, ∃ (m : ℕ) (c : Fin m → k) (a : Fin m → O),
        (∀ t, ∑ j, c j * χ t (a j) = if t = s then 1 else 0) ∧
        e s = ∑ j, algebraMap k K (c j) • ρ (a j) := by
  intro K _ C V _ _ _ L O k S _ _ _ _ _ χ hχ hk ρ hL hρ
  have hinj : Function.Injective (splitMap χ) := hχ.1
  have hsurj : Function.Surjective (splitMap χ) := hχ.2
  choose z hz using fun s : S => hsurj (Pi.single s 1)
  choose m c a hza using fun s : S => exists_sum_tmul (z s)
  have he : ∀ s, actMap (k := k) ρ (z s) = ∑ j, algebraMap k K (c s j) • ρ (a s j) := by
    intro s
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hza s, map_sum]
    exact Finset.sum_congr rfl fun j _ => actMap_tmul ρ _ _
  have hcoef : ∀ s t, ∑ j, c s j * χ t (a s j) = if t = s then 1 else 0 := by
    intro s t
    have h := congrFun (hz s) t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hza s, map_sum, Finset.sum_apply] at h
    simp only [splitMap_tmul] at h
    rw [h, Pi.single_apply]
  have hmul : ∀ s b, ρ b * actMap (k := k) ρ (z s) =
      algebraMap k K (χ s b) • actMap (k := k) ρ (z s) := by
    intro s b
    have h : ((1 : k) ⊗ₜ[ℤ] b) * z s = (χ s b ⊗ₜ[ℤ] (1 : O)) * z s := by
      apply hinj
      rw [map_mul, map_mul, hz s]
      funext t
      simp only [Pi.mul_apply, splitMap_tmul, Pi.single_apply]
      by_cases hts : t = s
      · subst hts; simp
      · simp [hts]
    have h' := congrArg (actMap (k := k) ρ) h
    rw [map_mul, map_mul, actMap_tmul, actMap_tmul] at h'
    simpa using h'
  have hsum : ∑ s, actMap (k := k) ρ (z s) = 1 := by
    have h : ∑ s, z s = 1 := by
      apply hinj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_one]
      simp only [hz]
      funext t
      simp [Finset.sum_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, h, map_one]
  refine ⟨fun s => actMap (k := k) ρ (z s), ?_, ?_, ?_, ?_, ?_⟩
  · intro s i x hx
    show actMap (k := k) ρ (z s) x ∈ L i
    rw [he s, LinearMap.sum_apply]
    exact sum_mem fun j _ => smul_mem_of_isBun C hL i (hk i _) (hρ _ i x hx)
  · intro s x
    simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker]
    intro b
    have h := congrArg (fun f : Module.End K V => f x) (hmul s b)
    simpa [sub_eq_zero] using h
  · intro s x hx
    simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    have hx' : ∀ b, ρ b x = algebraMap k K (χ s b) • x := fun b => by
      simpa [sub_eq_zero] using hx b
    show actMap (k := k) ρ (z s) x = x
    rw [he s, LinearMap.sum_apply]
    have : ∀ j, (algebraMap k K (c s j) • ρ (a s j)) x =
        algebraMap k K (c s j * χ s (a s j)) • x := fun j => by
      rw [LinearMap.smul_apply, hx', smul_smul, map_mul]
    simp only [this]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_smul, ← map_sum, hcoef s s]
    simp
  · intro x
    have h := congrArg (fun f : Module.End K V => f x) hsum
    simpa [LinearMap.sum_apply] using h
  · intro s
    exact ⟨m s, c s, a s, hcoef s, he s⟩

end GlobalTheory.CompanionTheory.Ar.Crv.SplitProj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsSectionLevel
section
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

variable {O : Type} [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
  [Module O L'] {B : LinearMap.BilinForm ℤ L} {B' : LinearMap.BilinForm ℤ L'}

theorem ProIso.exists_section_level [Module.Projective O L'] (f : ProIso O B B') (n : ℕ) :
    ∃ h : L' →ₗ[O] L, 0 < n → ∀ y, ∃ e, f.a n (h y) = y + n • e := by
  by_cases hn : 0 < n
  · let Ψ : L × L' →ₗ[O] L' := (f.a n).coprod (n • LinearMap.id)
    have hΨ : ∀ p : L × L', Ψ p = f.a n p.1 + n • p.2 := fun p => by
      simp only [Ψ, LinearMap.coprod_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hsurj : Function.Surjective Ψ := fun y => by
      obtain ⟨x, e, hxe⟩ := f.3 n hn y
      exact ⟨(x, e), by rw [hΨ, hxe]⟩
    obtain ⟨s, hs⟩ := Module.projective_lifting_property Ψ LinearMap.id hsurj
    refine ⟨LinearMap.fst O L L' ∘ₗ s, fun _ y => ⟨-(s y).2, ?_⟩⟩
    have hy := LinearMap.congr_fun hs y
    rw [LinearMap.comp_apply, hΨ, LinearMap.id_apply] at hy
    rw [LinearMap.comp_apply, LinearMap.fst_apply, smul_neg, ← sub_eq_add_neg,
      eq_sub_iff_add_eq, hy]
  · exact ⟨0, fun h => absurd h hn⟩

theorem ProIso.congr_of_map_congr (f : ProIso O B B') {n : ℕ} (hn : 0 < n) {x x' : L} {e : L'}
    (h : f.a n x = f.a n x' + n • e) : ∃ d, x = x' + n • d := by
  obtain ⟨d, hd⟩ := (f.inj n hn (x - x')).1 ⟨e, by rw [map_sub, h]; abel⟩
  exact ⟨d, by rw [← hd]; abel⟩

theorem ProIso.exists_isInv (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L]
    [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L')
    [Module.Projective O L'] (f : ProIso O B B') : ∃ g : ProIso O B' B, f.IsInv g := by
  choose h hh using fun n => GlobalTheory.CompanionTheory.Ar.ProIso.exists_section_level f n
  have hA : ∀ n, 0 < n → ∀ x : L, ∃ d, h n (f.a n x) = x + n • d := fun n hn x => by
    obtain ⟨e, he⟩ := hh n hn (f.a n x)
    exact GlobalTheory.CompanionTheory.Ar.ProIso.congr_of_map_congr f hn he
  refine ⟨⟨h, fun n hn y => ⟨?_, ?_⟩, fun n hn x => ?_, fun n hn x y => ?_,
    fun n m hn hm y => ?_⟩, ?_⟩
  · rintro ⟨z, hz⟩
    obtain ⟨e, he⟩ := hh n hn y
    rw [hz, map_nsmul] at he
    exact ⟨f.a n z - e, by rw [smul_sub, he]; abel⟩
  · rintro ⟨z, rfl⟩
    exact ⟨h n z, map_nsmul _ _ _⟩
  · obtain ⟨d, hd⟩ := hA n hn x
    exact ⟨f.a n x, -d, by rw [hd, smul_neg]; abel⟩
  · obtain ⟨e₁, he₁⟩ := hh n hn x
    obtain ⟨e₂, he₂⟩ := hh n hn y
    have d₁ := f.4 n hn (h n x) (h n y)
    have d₂ : (n : ℤ) ∣ B' (f.a n (h n x)) (f.a n (h n y)) - B' x y := by
      rw [he₁, he₂]
      simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
      exact ⟨B' x e₂ + B' e₁ y + n * B' e₁ e₂, by ring⟩
    have key : B (h n x) (h n y) - B' x y =
        (B' (f.a n (h n x)) (f.a n (h n y)) - B' x y) -
          (B' (f.a n (h n x)) (f.a n (h n y)) - B (h n x) (h n y)) := by ring
    rw [key]
    exact dvd_sub d₂ d₁
  · obtain ⟨e₁, he₁⟩ := hh (n * m) (Nat.mul_pos hn hm) y
    obtain ⟨e₂, he₂⟩ := f.5 n m hn hm (h (n * m) y)
    obtain ⟨e₃, he₃⟩ := hh n hn y
    refine GlobalTheory.CompanionTheory.Ar.ProIso.congr_of_map_congr f hn
      (e := m • e₁ - e₂ - e₃) ?_
    have h12 : f.a n (h (n * m) y) = y + (n * m) • e₁ - n • e₂ :=
      eq_sub_of_add_eq (he₂.symm.trans he₁)
    rw [h12, he₃, smul_sub, smul_sub, smul_smul]
    abel
  · show (∀ n, 0 < n → ∀ x : L, ∃ e, h n (f.a n x) = x + n • e) ∧
      ∀ n, 0 < n → ∀ y : L', ∃ e, f.a n (h n y) = y + n • e
    exact ⟨hA, hh⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsSymplecticBasisLagrangianBetween
section
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_saturation_torsionFree {Λ : Type*} [AddCommGroup Λ] (W : Submodule ℤ Λ) :
    ∃ S : Submodule ℤ Λ, (∀ x, x ∈ S ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W) ∧
      Module.IsTorsionFree ℤ (Λ ⧸ S) := by
  refine ⟨{ carrier := {x | ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W}
            add_mem' := ?_, zero_mem' := ⟨1, one_ne_zero, by simp⟩, smul_mem' := ?_ },
    fun x => Iff.rfl, ?_⟩
  · rintro a b ⟨k, hk, ha⟩ ⟨l, hl, hb⟩
    refine ⟨k * l, mul_ne_zero hk hl, ?_⟩
    rw [smul_add]
    refine W.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact W.smul_mem _ ha
    · rw [mul_smul]; exact W.smul_mem _ hb
  · rintro c a ⟨k, hk, ha⟩
    exact ⟨k, hk, by rw [smul_comm]; exact W.smul_mem _ ha⟩
  · rw [GlobalTheory.isTorsionFree_quotient_iff]
    rintro r x hr ⟨k, hk, hx⟩
    exact ⟨k * r, mul_ne_zero hk hr, by rw [mul_smul]; exact hx⟩

theorem exists_symplecticBasis_lagrangian_between : ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (B : LinearMap.BilinForm ℤ Λ), (∀ x, B x x = 0) → Function.Bijective B → Module.finrank ℤ Λ = 2 * g → ∀ W : Submodule ℤ Λ, (∀ x, (∀ y ∈ W, B x y = 0) → ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W) → ∃ bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ, (∀ i j, B (bas (.inl i)) (bas (.inl j)) = 0 ∧ B (bas (.inr i)) (bas (.inr j)) = 0 ∧ B (bas (.inl i)) (bas (.inr j)) = if i = j then 1 else 0) ∧ (∀ i, ∃ k : ℤ, k ≠ 0 ∧ k • bas (.inl i) ∈ W) ∧ ∀ x, (∀ y ∈ W, B x y = 0) → x ∈ Submodule.span ℤ (Set.range fun i => bas (.inl i)) := by
  intro g Λ _ _ _ B hB hp hg W hW
  have hA : B.IsAlt := hB
  obtain ⟨S, hS, hSt⟩ := exists_saturation_torsionFree W
  have hmem : ∀ x, x ∈ B.orthogonal S ↔ ∀ y ∈ W, B x y = 0 := by
    intro x
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h y hy
      exact hA.isRefl _ _ (h y ((hS y).2 ⟨1, one_ne_zero, by simpa using hy⟩))
    · intro h y hy
      obtain ⟨k, hk, hy⟩ := (hS y).1 hy
      have := h _ hy
      rw [map_smul, smul_eq_mul] at this
      exact hA.isRefl _ _ ((mul_eq_zero.1 this).resolve_left hk)
  have hoo : B.orthogonal (B.orthogonal S) = S :=
    GlobalTheory.orthogonal_orthogonal_of_isTorsionFree_quotient hA hp.2 hSt
  have hiso : B.orthogonal S ≤ B.orthogonal (B.orthogonal S) := by
    rw [hoo]
    intro x hx
    exact (hS x).2 (hW x ((hmem x).1 hx))
  let v := Module.finBasis ℤ (B.orthogonal S)
  obtain ⟨m, b, hb, hv⟩ := GlobalTheory.exists_isSymplecticBasis_extend hA hp
    (GlobalTheory.isTorsionFree_quotient_orthogonal B S) hiso v
  have hc := GlobalTheory.IsSymplecticBasisOfType.finrank_eq b
  have hc' : Fintype.card (Fin (Module.finrank ℤ (B.orthogonal S)) ⊕ Fin m) = g := by omega
  let σ := Fintype.equivFinOfCardEq hc'
  have hb' := hb.reindex σ
  have hl : ∀ i, (b.reindex (σ.sumCongr σ)) (.inl i) = b (.inl (σ.symm i)) := by
    intro i; simp
  refine ⟨b.reindex (σ.sumCongr σ), fun i j => ⟨hb'.left_left i j, hb'.right_right i j,
    hb'.left_right i j⟩, fun i => ?_, fun x hx => ?_⟩
  · refine (hS _).1 (hoo.le ((hb.orthogonal_eq_span hv).ge ?_))
    rw [hl]
    exact Submodule.subset_span (Or.inl ⟨_, rfl⟩)
  · have hx' := (hmem x).2 hx
    have h1 : x = ∑ i, v.repr ⟨x, hx'⟩ i • (v i : Λ) := by
      have := congrArg Subtype.val (v.sum_repr ⟨x, hx'⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    rw [h1]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨σ (.inl i), ?_⟩)
    simp only [hl, Equiv.symm_apply_apply, hv]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExtensionOrderEqSpan
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.ExtSpan

theorem extOrder_eq_span : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (R' : Type) [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) (g : T → R'), g ∈ extOrder φ A ↔ g ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} := by
  intro R _ T _ R' _ φ A g
  set S : Set (T → R') := {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} with hS
  have hmul : ∀ {x y : T → R'}, x ∈ S → y ∈ S → x * y ∈ S := by
    rintro _ _ ⟨f1, hf1, rfl⟩ ⟨f2, hf2, rfl⟩
    exact ⟨f1 * f2, A.mul_mem hf1 hf2, by funext t; simp [map_mul]⟩
  have hone : (1 : T → R') ∈ S := ⟨1, A.one_mem, by funext t; simp⟩
  let M : Submonoid (T → R') := { carrier := S, mul_mem' := hmul, one_mem' := hone }
  have hcl : ((Submonoid.closure S : Submonoid (T → R')) : Set (T → R')) = S :=
    congrArg (fun N : Submonoid (T → R') => (N : Set (T → R'))) (Submonoid.closure_eq M)
  have hspan : Subalgebra.toSubmodule (Algebra.adjoin R' S) = Submodule.span R' S := by
    rw [Algebra.adjoin_eq_span, hcl]
  have hdef : extOrder φ A = Algebra.adjoin R' S := by
    first
    | rfl
    | (unfold extOrder; congr 1)
    | (unfold extOrder; congr 1; ext x; simp only [hS, Set.mem_setOf_eq, Set.mem_range, Set.mem_image, Subtype.exists, exists_prop, SetLike.mem_coe]; constructor <;> rintro ⟨f, hf, h⟩ <;> exact ⟨f, hf, h.symm⟩)
  rw [hdef, ← Subalgebra.mem_toSubmodule, hspan]

end GlobalTheory.CompanionTheory.Ar.BT.ExtSpan
end

