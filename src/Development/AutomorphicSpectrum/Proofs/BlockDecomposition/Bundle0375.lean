module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.AutomorphicSpectrum.Definitions.JetCones.SymCapRev
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AutomorphicSpectrum.Proofs.JetProofs.EvFirst
public import Development.AutomorphicSpectrum.Proofs.JetProofs.GraphExtend
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.NoSecondTypeWeight
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightTensorDecomposition
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.ExtHw

theorem inner_word_eq_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : Fin n → Fin n → Module.End ℂ H) (μ : Fin n → ℝ) (hR : Formalism.REAL.GlRel D)
    (hA : ∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ) (Hs : Submodule ℂ H)
    (hs : ∀ x ∈ Hs, Formalism.REAL.KHighest (fun _ => true) D μ x) {x y : H} (hx : x ∈ Hs) (hy : y ∈ Hs)
    (hxx : ⟪x, x⟫_ℂ = 1) (hyy : ⟪y, y⟫_ℂ = 1) (hxy : ⟪x, y⟫_ℂ = 0)
    (l : List (Fin n × Fin n)) : ⟪x, (l.map fun z => D z.1 z.2).prod y⟫_ℂ = 0 := by
  have hyx : ⟪y, x⟫_ℂ = 0 := by rw [← inner_conj_symm, hxy, map_zero]
  have vev : ∀ u ∈ Hs, ∀ v ∈ Hs,
      ⟪u, (l.map fun z => D z.1 z.2).prod u⟫_ℂ * ⟪v, v⟫_ℂ =
        ⟪v, (l.map fun z => D z.1 z.2).prod v⟫_ℂ * ⟪u, u⟫_ℂ := fun u hu v hv =>
    GlobalTheory.CompanionTheory.AlgRepEndIrreducible.Vev.vev_eq n (fun _ => true) H H D D μ u v (fun a b c d _ _ => hR a b c d)
      (fun a b c d _ _ => hR a b c d) (fun a b _ => hA a b) (fun a b _ => hA a b)
      (hs u hu) (hs v hv) l (fun _ _ => rfl)
  generalize (l.map fun z => D z.1 z.2).prod = W at vev ⊢
  have h1 := vev x hx y hy
  have h2 := vev (x + y) (Hs.add_mem hx hy) x hx
  have h3 := vev (x + Complex.I • y) (Hs.add_mem hx (Hs.smul_mem _ hy)) x hx
  simp only [map_add (f := _), map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hxx, hyy, hxy, hyx, Complex.conj_I] at h1 h2 h3
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h4 : ⟪x, W y⟫_ℂ + ⟪y, W x⟫_ℂ = 0 := by linear_combination h2 + h1
  have h5 : Complex.I * (⟪x, W y⟫_ℂ - ⟪y, W x⟫_ℂ) = 0 := by
    linear_combination h3 + h1 + (⟪y, W y⟫_ℂ - ⟪x, W x⟫_ℂ) * hI
  have h6 : ⟪x, W y⟫_ℂ - ⟪y, W x⟫_ℂ = 0 :=
    (mul_eq_zero.1 h5).resolve_left Complex.I_ne_zero
  linear_combination (1 / 2 : ℂ) * h4 + (1 / 2 : ℂ) * h6

theorem kmap_extend : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (D : Fin n → Fin n → Module.End ℂ H) (D' : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ), Formalism.REAL.GlRel D → Formalism.REAL.GlRel D' → (∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ) → (∀ a b (x y : V), ⟪D' a b x, y⟫_ℂ = ⟪x, D' b a y⟫_ℂ) → ∀ Hs : Submodule ℂ H, (∀ x ∈ Hs, Formalism.REAL.KHighest (fun _ => true) D μ x) → ∀ f : Hs →ₗ[ℂ] V, (∀ x, Formalism.REAL.KHighest (fun _ => true) D' μ (f x)) → ∃ T : H →ₗ[ℂ] V, (∀ x : Hs, T x = f x) ∧ ∀ a b w, T (D a b w) = D' a b (T w) := by
  intro n H V _ _ _ _ _ D D' μ hR hR' hA hA' Hs hs f hf
  let ξ := stdOrthonormalBasis ℂ Hs
  have hself : ∀ i, ⟪(ξ i : H), (ξ i : H)⟫_ℂ = 1 := fun i => by
    have := (orthonormal_iff_ite.1 ξ.orthonormal) i i
    rw [if_pos rfl] at this
    exact this
  have hoff : ∀ i j, i ≠ j → ⟪(ξ i : H), (ξ j : H)⟫_ℂ = 0 := fun i j hij => by
    have := (orthonormal_iff_ite.1 ξ.orthonormal) i j
    rw [if_neg hij] at this
    exact this
  have hne : ∀ i, (ξ i : H) ≠ 0 := fun i h0 => by
    have := hself i
    rw [h0, inner_zero_left] at this
    exact zero_ne_one this
  have hex : ∀ i, ∃ T : H →ₗ[ℂ] V, T (ξ i : H) = f (ξ i) ∧ GlobalTheory.CompanionTheory.AlgRepEndIrreducible.KMap (fun _ => true) D D' T :=
    fun i => GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap.hwmap n (fun _ => true) H V D D' μ (ξ i : H) (f (ξ i))
      (fun a b c d _ _ => hR a b c d) (fun a b c d _ _ => hR' a b c d)
      (fun a b _ => hA a b) (fun a b _ => hA' a b) (hs _ (ξ i).2) (hf _) (hne i)
  choose Ti hTi hTK using hex
  let Z : _ → Submodule ℂ H := fun i => Submodule.span ℂ
    (Set.range fun l : List (Fin n × Fin n) => (l.map fun z => D z.1 z.2).prod (ξ i : H))
  have hst : ∀ i a b, ∀ z ∈ Z i, D a b z ∈ Z i := by
    intro i a b z hz
    induction hz using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact Submodule.subset_span ⟨(a, b) :: l, by simp⟩
  have hperp : ∀ i a b, ∀ z ∈ (Z i)ᗮ, D a b z ∈ (Z i)ᗮ := by
    intro i a b z hz
    rw [Submodule.mem_orthogonal] at hz ⊢
    intro u hu
    rw [← hA b a]
    exact hz _ (hst i b a u hu)
  have hcomm : ∀ i a b w, (Z i).starProjection (D a b w) = D a b ((Z i).starProjection w) := by
    intro i a b w
    obtain ⟨u, hu, z, hz, rfl⟩ := (Z i).exists_add_mem_mem_orthogonal w
    have e1 : (Z i).starProjection u = u := Submodule.starProjection_eq_self_iff.2 hu
    have e2 : (Z i).starProjection z = 0 := (Submodule.starProjection_apply_eq_zero_iff _).2 hz
    have e3 : (Z i).starProjection (D a b u) = D a b u :=
      Submodule.starProjection_eq_self_iff.2 (hst i a b u hu)
    have e4 : (Z i).starProjection (D a b z) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff _).2 (hperp i a b z hz)
    rw [map_add (f := _), map_add (f := _), map_add (f := _), e1, e2, e3, e4, add_zero, add_zero]
  have hdiag : ∀ i, (Z i).starProjection (ξ i : H) = ξ i := fun i =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.subset_span ⟨[], by simp⟩)
  have hzero : ∀ i j, i ≠ j → (Z i).starProjection (ξ j : H) = 0 := by
    intro i j hij
    refine (Submodule.starProjection_apply_eq_zero_iff _).2 ?_
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      rw [GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap.word_adj (ε := fun _ => true) (fun a b _ => hA a b) l (fun _ _ => rfl)]
      exact inner_word_eq_zero D μ hR hA Hs hs (ξ i).2 (ξ j).2 (hself i) (hself j) (hoff i j hij) _
  let T : H →ₗ[ℂ] V := ∑ i, (Ti i).comp ((Z i).starProjection : H →L[ℂ] H).toLinearMap
  have hTapp : ∀ w, T w = ∑ i, Ti i ((Z i).starProjection w) := fun w => by
    simp [T, LinearMap.sum_apply]
  refine ⟨T, ?_, ?_⟩
  · have hb : T.comp Hs.subtype = f := by
      refine ξ.toBasis.ext fun j => ?_
      rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, Submodule.subtype_apply, hTapp,
        Finset.sum_eq_single j]
      · rw [hdiag, hTi]
      · intro i _ hij
        rw [hzero i j hij, map_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    intro x
    exact LinearMap.congr_fun hb x
  · intro a b w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hTapp, hTapp, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcomm, hTK i a b rfl]

end GlobalTheory.CompanionTheory.RealCount.ExtHw
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFixedNonzero
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.SmInd

def bump {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (P : Subgroup G)
    (σ : Representation ℂ P W) (K : Subgroup G) (x : W) (g : G) : W :=
  if h : ∃ p : P, (p : G)⁻¹ * g ∈ K then σ h.choose x else 0

variable {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] {P : Subgroup G}
  {σ : Representation ℂ P W} {K : Subgroup G} {x : W}

theorem bump_eq (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) {p : P} {g : G}
    (hp : (p : G)⁻¹ * g ∈ K) : bump P σ K x g = σ p x := by
  have h : ∃ p : P, (p : G)⁻¹ * g ∈ K := ⟨p, hp⟩
  have hq := h.choose_spec
  rw [bump, dite_eq_left h]
  set q := h.choose
  have hm : ((q⁻¹ * p : P) : G) ∈ K := by
    have := K.mul_mem hq (K.inv_mem hp)
    have e : (q : G)⁻¹ * g * ((p : G)⁻¹ * g)⁻¹ = ((q⁻¹ * p : P) : G) := by
      simp [mul_assoc]
    rwa [e] at this
  have h2 := hx _ hm
  have h3 : σ p x = σ q (σ (q⁻¹ * p) x) := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  rw [h3, h2]

theorem bump_of_not {g : G} (h : ¬ ∃ p : P, (p : G)⁻¹ * g ∈ K) : bump P σ K x g = 0 := by
  rw [bump, dite_eq_right h]

theorem bump_mul_left (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) (p : P) (g : G) :
    bump P σ K x ((p : G) * g) = σ p (bump P σ K x g) := by
  by_cases h : ∃ q : P, (q : G)⁻¹ * g ∈ K
  · obtain ⟨q, hq⟩ := h
    have hq' : (((p * q : P) : G))⁻¹ * ((p : G) * g) ∈ K := by
      have e : (((p * q : P) : G))⁻¹ * ((p : G) * g) = (q : G)⁻¹ * g := by
        simp [mul_assoc]
      rwa [e]
    rw [bump_eq hx hq', bump_eq hx hq, map_mul, Module.End.mul_apply]
  · have h' : ¬ ∃ r : P, (r : G)⁻¹ * ((p : G) * g) ∈ K := by
      rintro ⟨r, hr⟩
      refine h ⟨p⁻¹ * r, ?_⟩
      have e : (((p⁻¹ * r : P) : G))⁻¹ * g = (r : G)⁻¹ * ((p : G) * g) := by
        simp [mul_assoc]
      rwa [e]
    rw [bump_of_not h, bump_of_not h', map_zero]

theorem bump_mul_right (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) (g : G) {k : G} (hk : k ∈ K) :
    bump P σ K x (g * k) = bump P σ K x g := by
  by_cases h : ∃ q : P, (q : G)⁻¹ * g ∈ K
  · obtain ⟨q, hq⟩ := h
    have hq' : (q : G)⁻¹ * (g * k) ∈ K := by
      rw [← mul_assoc]; exact K.mul_mem hq hk
    rw [bump_eq hx hq', bump_eq hx hq]
  · have h' : ¬ ∃ r : P, (r : G)⁻¹ * (g * k) ∈ K := by
      rintro ⟨r, hr⟩
      refine h ⟨r, ?_⟩
      have := K.mul_mem hr (K.inv_mem hk)
      have e : (r : G)⁻¹ * (g * k) * k⁻¹ = (r : G)⁻¹ * g := by simp [mul_assoc]
      rwa [e] at this
    rw [bump_of_not h, bump_of_not h']

theorem bump_one (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) : bump P σ K x 1 = x := by
  have h : ((1 : P) : G)⁻¹ * 1 ∈ K := by simp [K.one_mem]
  rw [bump_eq hx h]; simp

def bumpInd (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) : indSpace P σ :=
  ⟨bump P σ K x, fun p g => bump_mul_left hx p g⟩

theorem ind_bumpInd (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) {k : G} (hk : k ∈ K) :
    ind P σ k (bumpInd hx) = bumpInd hx := by
  apply Subtype.ext
  funext g
  exact bump_mul_right hx g hk

theorem fixed_smInd_ne_bot [TopologicalSpace G] [IsTopologicalGroup G] (hK : IsOpen (K : Set G))
    (hx0 : x ≠ 0) (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) : fixed (smInd P σ) K ≠ ⊥ := by
  have hs : bumpInd hx ∈ smoothPart (ind P σ) :=
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds K.one_mem)
      fun k hk => ind_bumpInd hx hk)
  refine (Submodule.ne_bot_iff _).2 ⟨⟨bumpInd hx, hs⟩, ?_, ?_⟩
  · intro k
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact Subtype.ext (ind_bumpInd hx k.2)
  · intro h
    apply hx0
    have h1 := congrFun (congrArg (fun φ : smoothPart (ind P σ) => (φ.1 : G → W)) h) 1
    rw [← bump_one hx]
    exact h1

theorem fixed_smInd_ne_bot_of_fixed : ∀ (G W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (P : Subgroup G) (σ : Representation ℂ P W) (K : Subgroup G), IsOpen (K : Set G) → ∀ x : W, x ≠ 0 → (∀ p : P, (p : G) ∈ K → σ p x = x) → fixed (smInd P σ) K ≠ ⊥ :=
  fun _ _ _ _ _ _ _ _ _ _ hK _ hx0 hx => fixed_smInd_ne_bot hK hx0 hx

end GlobalTheory.CompanionTheory.SmInd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfNotInCodimOneSubmodule
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RgGuCore

theorem not_inf_le_of_rank_quotient_le_one {V : Type} [AddCommGroup V] [Module ℂ V]
    (T A C : Submodule ℂ V) (hT : Module.rank ℂ (V ⧸ T) ≤ 1)
    (hmod : (A ⊔ C) ⊓ T ≤ A ⊓ T ⊔ C ⊓ T) (hA : ¬ A ≤ T) (hC : ¬ C ≤ T) :
    ¬ A ⊓ C ≤ T := by
  obtain ⟨a, haA, haT⟩ := SetLike.not_le_iff_exists.mp hA
  obtain ⟨c, hcC, hcT⟩ := SetLike.not_le_iff_exists.mp hC
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp hT
  obtain ⟨s, hs⟩ := hv₀ (Submodule.Quotient.mk a)
  obtain ⟨t, ht⟩ := hv₀ (Submodule.Quotient.mk c)
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply haT
    rw [← Submodule.Quotient.mk_eq_zero T, ← hs, zero_smul]
  have hdiff : c - (t * s⁻¹) • a ∈ T := by
    rw [← Submodule.Quotient.mk_eq_zero T, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      ← hs, ← ht, smul_smul, mul_assoc, inv_mul_cancel₀ hs0, mul_one, sub_self]
  have hsum : c - (t * s⁻¹) • a ∈ A ⊔ C :=
    Submodule.sub_mem _ (Submodule.mem_sup_right hcC)
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ haA))
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (hmod (Submodule.mem_inf.mpr ⟨hsum, hdiff⟩))
  rw [Submodule.mem_inf] at hx hy
  have hw : c - y = (t * s⁻¹) • a + x := by
    calc c - y = (c - (t * s⁻¹) • a - (x + y)) + (t * s⁻¹) • a + x := by abel
      _ = (t * s⁻¹) • a + x := by rw [hxy, sub_self, zero_add]
  have hwA : c - y ∈ A := hw ▸ Submodule.add_mem _ (Submodule.smul_mem _ _ haA) hx.1
  have hwC : c - y ∈ C := Submodule.sub_mem _ hcC hy.1
  intro h
  apply hcT
  have hwT : c - y ∈ T := h (Submodule.mem_inf.mpr ⟨hwA, hwC⟩)
  simpa using Submodule.add_mem _ hwT hy.2

theorem gen_core_meet {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (T : Submodule ℂ V) (hT : Module.rank ℂ (V ⧸ T) ≤ 1)
    (A C : Subrepresentation ρ)
    (hmod : (A ⊔ C).toSubmodule ⊓ T ≤ A.toSubmodule ⊓ T ⊔ C.toSubmodule ⊓ T)
    (hA : ¬ A.toSubmodule ≤ T) (hC : ¬ C.toSubmodule ≤ T) :
    ¬ (A ⊓ C).toSubmodule ≤ T := by
  rw [Subrepresentation.toSubmodule_sup] at hmod
  rw [Subrepresentation.toSubmodule_inf]
  exact GlobalTheory.CompanionTheory.RgGuCore.not_inf_le_of_rank_quotient_le_one T A.toSubmodule C.toSubmodule hT hmod hA hC

end GlobalTheory.CompanionTheory.RgGuCore
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
section
noncomputable section

open Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.PairMult

open Formalism.REAL (GlRel qdet)
open CompanionTheory.D.LK (Pos)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

abbrev Lt (n : ℕ) : Type := Bool × Pos n

abbrev Cq (n : ℕ) (V : Type) : Type := Finset (Lt n) → V

def keyL (l : Lt n) : ℕ := (if l.1 then 0 else (n + 1) * (n + 1)) + CompanionTheory.D.LK.key l.2

def sgL (l : Lt n) (A : Finset (Lt n)) : ℂ := (-1) ^ (A.filter fun j => keyL j < keyL l).card

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def annq (l : Lt n) : Module.End ℂ (Cq n V) where
  toFun x := fun A => if l ∈ A then 0 else sgL l A • x (insert l A)
  map_add' x y := by funext A; by_cases h : l ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : l ∈ A <;> simp [h, smul_comm c]

def creq (l : Lt n) : Module.End ℂ (Cq n V) where
  toFun x := fun A => if l ∈ A then sgL l A • x (A.erase l) else 0
  map_add' x y := by funext A; by_cases h : l ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : l ∈ A <;> simp [h, smul_comm c]

def liftq (n : ℕ) {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') : Cq n V →ₗ[ℂ] Cq n V' :=
  T.compLeft (Finset (Lt n))

def Ts (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (p q : Fin n) : Module.End ℂ V :=
  if s then E1 p q + E2 p q else E1 p q - E2 p q

def Tl (E1 E2 : Fin n → Fin n → Module.End ℂ V) (l : Lt n) : Module.End ℂ V := Ts E1 E2 l.1 l.2.1.1 l.2.1.2

def bdq (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Cq n V) :=
  (∑ l : Lt n, (liftq n (Tl E1 E2 l) : Module.End ℂ (Cq n V)) * annq l) +
    ∑ s : Bool, ∑ t : Bool, ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      if i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then creq ((s == t), k) * annq (t, j) * annq (s, i) else 0

def SuppQ (P : Lt n → Prop) (y : Cq n V) : Prop := ∀ A, y A ≠ 0 → ∀ l ∈ A, P l

def DegQ (j : ℕ) (y : Cq n V) : Prop := ∀ A, y A ≠ 0 → A.card = j

def adLq (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  ∑ t : Bool, ∑ i : Pos n, ∑ k : Pos n, CompanionTheory.RgExh.U.adC p q i k • (creq ((s == t), k) * annq (t, i))

def lFq (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  liftq n (Ts E1 E2 s p q) + adLq s p q

def c1 (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (lFq E1 E2 true p q + lFq E1 E2 false p q)

def c2 (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (lFq E1 E2 true p q - lFq E1 E2 false p q)

end Chains

abbrev inUL (lev : Fin n → ℕ) (l : Lt n) : Prop := lev l.2.1.1 < lev l.2.1.2

abbrev inKU (lev : Fin n → ℕ) (l : Lt n) : Prop := l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2

def omQ (lev : Fin n → ℕ) : Finset (Lt n) := univ.filter fun l => l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2

def topq {V : Type} [AddCommGroup V] [Module ℂ V] (lev : Fin n → ℕ) (v : V) : Cq n V := Pi.single (omQ lev) v

def IsSubL (lev : Fin n → ℕ) (S : Lt n → Prop) : Prop :=
  (∀ l, S l → inUL lev l) ∧ ∀ (s t : Bool) (i j k : Pos n), i.1.2 = j.1.1 → k.1.1 = i.1.1 → k.1.2 = j.1.2 →
    S (s, i) → S (t, j) → S ((s == t), k)

section Algebra

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def PairRel (E1 E2 : Fin n → Fin n → Module.End ℂ W) : Prop :=
  GlRel E1 ∧ GlRel E2 ∧ ∀ a b c d, Commute (E1 a b) (E2 c d)

def ev2 (E1 E2 : Fin n → Fin n → Module.End ℂ W) : FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] Module.End ℂ W :=
  FreeAlgebra.lift ℂ fun x => if x.1 then E1 x.2.1 x.2.2 else E2 x.2.1 x.2.2

def evB (lev : Fin n → ℕ) (X1 X2 : Fin n → Fin n → Module.End ℂ W) :
    FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] Module.End ℂ W :=
  FreeAlgebra.lift ℂ fun x => if lev x.2.1 = lev x.2.2 then (if x.1 then X1 x.2.1 x.2.2 else X2 x.2.1 x.2.2) else 0

def LRel (lev : Fin n → ℕ) (X1 X2 : Fin n → Fin n → Module.End ℂ W) : Prop :=
  (∀ p q r v, lev p = lev q → lev r = lev v →
    X1 p q * X1 r v - X1 r v * X1 p q = (if q = r then X1 p v else 0) - (if v = p then X1 r q else 0)) ∧
  (∀ p q r v, lev p = lev q → lev r = lev v →
    X2 p q * X2 r v - X2 r v * X2 p q = (if q = r then X2 p v else 0) - (if v = p then X2 r q else 0)) ∧
  ∀ p q r v, lev p = lev q → lev r = lev v → Commute (X1 p q) (X2 r v)

end Algebra

def Inv2 (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
    ∀ c d, Commute (E1 c d + E2 c d) (ev2 E1 E2 a)

def InvLev (lev : Fin n → ℕ) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W), LRel lev X1 X2 →
    ∀ p q, lev p = lev q → Commute (X1 p q + X2 p q) (evB lev X1 X2 b)

def LiftInv : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
    (∀ a b (x y : V), ⟪kF E1 E2 a b x, y⟫_ℂ = ⟪x, kF E1 E2 b a y⟫_ℂ) →
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF E1 E2 a b w ∈ S) →
    ∀ v w : V, v ≠ 0 → v ∈ hwSp E1 E2 μ → w ∈ hwSp E1 E2 μ → (∃ x ∈ alg E1 E2, x v = w) →
      ∃ a, Inv2 a ∧ ev2 E1 E2 a v = w

def HCDec2 : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)), Monotone lev → Inv2 a →
    ∃ b : FreeAlgebra ℂ (Bool × Fin n × Fin n), ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 → ∀ x : V, ∃ w : Lt n → V,
        ev2 E1 E2 a x - evB lev E1 E2 b x = ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0

def GenCOU2 : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (S : Lt n → Prop) (a b : FreeAlgebra ℂ (Bool × Fin n × Fin n)), Monotone lev → IsSubL lev S →
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
      (∀ l, S l → Commute (Tl E1 E2 l) (ev2 E1 E2 a)) ∧
      ∀ x : V, ∃ w : Lt n → V, ev2 E1 E2 a x - evB lev E1 E2 b x = ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), PairRel E1 E2 →
      ∀ (j : ℕ) (x : Cq n V), SuppQ S x → DegQ j x → bdq E1 E2 x = 0 →
        ∃ w : Cq n V, SuppQ (inUL lev) w ∧ DegQ (j + 1) w ∧
          liftq n (ev2 E1 E2 a) x - evB lev (c1 E1 E2) (c2 E1 E2) b x = bdq E1 E2 w

def TopCyc : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    PairRel E1 E2 → ∀ v : V, (∀ l, inKU lev l → Tl E1 E2 l v = 0) → bdq E1 E2 (topq lev v) = 0

def LeviRel : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    Monotone lev → PairRel E1 E2 → ∀ x : Cq n V, SuppQ (inUL lev) x →
      (∀ s p q, lev p = lev q → SuppQ (inUL lev) (lFq E1 E2 s p q x) ∧ (∀ j, DegQ j x → DegQ j (lFq E1 E2 s p q x)) ∧
        lFq E1 E2 s p q (bdq E1 E2 x) = bdq E1 E2 (lFq E1 E2 s p q x)) ∧
      ∀ p q r v, lev p = lev q → lev r = lev v →
        (c1 E1 E2 p q (c1 E1 E2 r v x) - c1 E1 E2 r v (c1 E1 E2 p q x) =
          (if q = r then c1 E1 E2 p v x else 0) - (if v = p then c1 E1 E2 r q x else 0)) ∧
        (c2 E1 E2 p q (c2 E1 E2 r v x) - c2 E1 E2 r v (c2 E1 E2 p q x) =
          (if q = r then c2 E1 E2 p v x else 0) - (if v = p then c2 E1 E2 r q x else 0)) ∧
        c1 E1 E2 p q (c2 E1 E2 r v x) = c2 E1 E2 r v (c1 E1 E2 p q x)

def InvL : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W)
    (L : Submodule ℂ W) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)), LRel lev X1 X2 →
    (∀ p q, lev p = lev q → ∀ s ∈ L, (X1 p q + X2 p q) s ∈ L) →
    (∀ p q, lev p = lev q → ∀ s ∈ L, (X1 p q + X2 p q) (evB lev X1 X2 b s) = evB lev X1 X2 b ((X1 p q + X2 p q) s)) →
    ∃ b', InvLev lev b' ∧ ∀ s ∈ L, evB lev X1 X2 b' s = evB lev X1 X2 b s

def CapOne : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ),
    GlRel E → (∀ m (x : V), gelA E m x = GlobalTheory.Dec.gelfVal χ m • x) →
      ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V)

def DualCap : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ),
    GlRel E → (∀ m (x : V), gelA (barF E) m x = GlobalTheory.Dec.gelfVal (fun a => -χ a) m • x) →
      ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V)

end GlobalTheory.CompanionTheory.PairMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetHeckeConditionHolds
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.HeckeExist

theorem exists_heckeOp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.CH k := by
  intro k _ _ _ _ N J _ hJc V _ _ π hπ g
  obtain ⟨E, hE1, -, hE3, -, -⟩ :=
    GlobalTheory.CompanionTheory.CompactAvg.exists_average (GL (Fin N) k) J hJc V π hπ
  refine ⟨((E ∘ₗ π g ∘ₗ (fixed π J).subtype).codRestrict (fixed π J) (fun v => hE1 _)), ?_⟩
  intro v l hl
  have h := LinearMap.congr_fun (hE3 l hl) (π g (v : V))
  simpa using h.symm

end GlobalTheory.CompanionTheory.HeckeExist
end

