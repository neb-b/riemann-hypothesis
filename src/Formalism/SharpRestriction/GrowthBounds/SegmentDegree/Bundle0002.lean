module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.StrictMonoIntExists

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNeZeroOfResidueNeZero
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def zSeg (O : Type) [CommRing O] (j : ℤ) (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ) : SegRing O r K :=
  plEmb O r K (X.DlSeg p K O j) * expand (p ^ X.Rj p K j) y * monomial e 1

def IsEll (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : Prop :=
  (∀ v, e v ≠ 0 → v.1 ∈ X.toLate j) ∧ ∀ v, e v < p ^ X.Rj p K j

def Step2 (j : ℤ) (b : ℤ → ℕ) : Prop :=
  ∀ z ∈ X.F.LLset j,
    (X.a' p K (posOf n' z) : ℝ) / (p : ℝ) ^ (X.F.dist j z + X.Rj p K j) - k (r := r) K < (b z : ℝ)

end Dat

def CoarseLabelFactorisation : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O],
    X.Hyp p K → ∀ l, X.IsCLabel p K l →
    ∃ (l0 : Fin n' × Fin (r + K) →₀ ℕ) (e : ℤ → (ℤ × Fin (r + K) →₀ ℕ)), IsLabel p X.F l0 ∧
      (∀ j, X.IsEll p K j (e j)) ∧
      (monomial l 1 : RRing O n' (r + K)) =
        monomial l0 1 * ∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) (monomial (e j) 1)

def TopDegreeComparison : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O],
    X.Hyp p K → ∀ (b : ℤ → ℤ → ℕ) (y : ℤ → SegRing O r K) (l : Fin n' × Fin (r + K) →₀ ℕ),
      (∀ j, y j ∈ X.Mj p K O j (b j)) → X.IsCLabel p K l →
      (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y j)) * monomial l 1 ∈ RRdeg O n' (r + K) (X.a' p K) →
      (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y j)) * monomial l 1 ≠ 0 →
      ∀ j ∈ Finset.range X.F.J, X.Step2 p K (j : ℤ) (b j)

def DiscriminantMultihomogeneous : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O],
    X.Dl p K O ∈ RRdeg O n' (r + K) (X.Et p K)

def DiscriminantNeZero : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], X.Hyp p K → X.Dl p K O ≠ 0

theorem discriminant_ne_zero_of_residue_ne_zero (h : DiscriminantNonzeroModUniformiser) : DiscriminantNeZero := by
  intro p n' r K _ _ _ X O _ _ _ hX h0
  exact h p n' r K X O hX (by rw [h0, map_zero])

def TopCountLowerBounds (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    (∀ t ∈ X.F.TT, (9 / 10 : ℝ) * (X.deg t : ℝ) ≤ (X.a' p K t : ℝ)) ∧ ∀ t, X.Et p K t ≤ X.d t

def SegmentReductionLiftsMultihomogeneous (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ) (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ),
      y ∈ X.Mj p K O j b → X.IsEll p K j e → X.Step2 p K j b →
      ∀ β : ℤ → ℕ, X.zSeg p K O j y e ∈ Pol O (r + K) β →
      ∃ x ∈ X.XXs p K O j, x ∈ Pol O (r + K) β ∧
        MvPolynomial.map (IsLocalRing.residue O) x = MvPolynomial.map (IsLocalRing.residue O) (X.zSeg p K O j y e)

def SegmentImageMultihomogeneous : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O]
    (j : ℤ) (b : ℤ → ℕ) (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ),
    y ∈ Pol O (r + K) b → ∃ β : ℤ → ℕ, X.zSeg p K O j y e ∈ Pol O (r + K) β

def SegmentProductDegreeDetermined : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] (F : Frames n' r) (O : Type) [CommRing O]
    (x z : ℤ → SegRing O r K) (β : ℤ → ℤ → ℕ) (l0 : Fin n' × Fin (r + K) →₀ ℕ) (d : Fin n' → ℕ),
    (∀ j, x j ∈ Pol O (r + K) (β j)) → (∀ j, z j ∈ Pol O (r + K) (β j)) →
    (∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (z j)) * monomial l0 1 ∈ RRdeg O n' (r + K) d →
    (∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (z j)) * monomial l0 1 ≠ 0 →
    (∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (x j)) * monomial l0 1 ∈ RRdeg O n' (r + K) d

theorem RRdeg_eq_Pol (O : Type) [CommRing O] (n' k : ℕ) (d : Fin n' → ℕ) : RRdeg O n' k d = Pol O k d := rfl

theorem segDeg_eq_Pol (O : Type) [CommRing O] (r K : ℕ) (b : ℤ → ℕ) :
    restrictSupport O (Dat.segDegSet (r := r) K b) = Pol O (r + K) b := rfl

theorem map_phSeg {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (K p : ℕ) {n' r : ℕ} [NeZero n']
    (F : Frames n' r) (j : ℤ) (P : SegRing R r K) :
    MvPolynomial.map f (phSeg R K p F j P) = phSeg S K p F j (MvPolynomial.map f P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [phSeg]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | mul_X q v h =>
    simp only [map_mul, h, map_X]
    simp [phSeg]

theorem phc_eq {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (O : Type) [CommRing O] (j : ℤ) (y : SegRing O r K) :
    X.phc p K O j y = phSeg O K p X.F j (expand (p ^ X.Rj p K j) y) := by
  have : X.phc p K O j = (phSeg O K p X.F j).comp (expand (p ^ X.Rj p K j)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Dat.phc, phSeg, AlgHom.comp_apply, expand_X, aeval_X, map_pow]
    rw [← pow_mul, ← pow_add]
  rw [this]; rfl

theorem generator_of_segment_reductions (C₀ : ℝ) (hLab : CoarseLabelFactorisation) (hDeg2 : TopDegreeComparison) (hDlHom : DiscriminantMultihomogeneous) (hDlNe : DiscriminantNeZero)
    (h41b : TopCountLowerBounds C₀) (hSeg : SegmentReductionLiftsMultihomogeneous C₀) (hZ : SegmentImageMultihomogeneous) (hHom : SegmentProductDegreeDetermined) : GeneratorModuloUniformiser C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk u hu
  obtain ⟨b, y, l, hy, hl, hueq, hdeg⟩ := hu
  have hJ : 1 ≤ X.F.J := hX.valid.1
  have hp0 : 0 < p := hX.prime.pos
  by_cases hu0 : u = 0
  · refine ⟨0, ⟨fun _ => 0, fun _ => Submodule.zero_mem _, 0, ?_, ?_, Submodule.zero_mem _⟩, by simp [hu0]⟩
    · intro j x _ _ c
      simpa using Nat.pow_pos hp0
    · have h0 : (∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) ((fun _ : ℤ => (0 : SegRing O r K)) (j : ℤ))) = 0 :=
        Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr hJ) (map_zero _)
      rw [h0, zero_mul]
  obtain ⟨l0, e, hl0, he, hmon⟩ := hLab p n' r K X O hX l hl
  set z : ℤ → SegRing O r K := fun j => X.zSeg p K O j (y j) (e j) with hz
  have hDu : X.Dl p K O * u = (∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) (z j)) * monomial l0 1 := by
    rw [hueq, hmon]
    simp only [hz, Dat.zSeg, Dat.Dl, map_mul, Finset.prod_mul_distrib, phc_eq]
    ring
  have hβ : ∀ j, ∃ β : ℤ → ℕ, z j ∈ Pol O (r + K) β := fun j =>
    hZ p n' r K X O j (b j) (y j) (e j) (by rw [← segDeg_eq_Pol]; exact (hy j).1.2)
  choose β hβ using hβ
  have h2 := hDeg2 p n' r K X O hX b y l hy hl (hueq ▸ hdeg) (hueq ▸ hu0)
  have hx : ∀ j : ℤ, ∃ x, x ∈ X.XXs p K O j ∧ x ∈ Pol O (r + K) (β j) ∧
      ((∃ i ∈ Finset.range X.F.J, (i : ℤ) = j) →
        MvPolynomial.map (IsLocalRing.residue O) x = MvPolynomial.map (IsLocalRing.residue O) (z j)) := by
    intro j
    by_cases hj : ∃ i ∈ Finset.range X.F.J, (i : ℤ) = j
    · obtain ⟨i, hi, rfl⟩ := hj
      obtain ⟨x, h1, h2', h3⟩ := hSeg p n' r K X O S hX hLa hk (i : ℤ) (b i) (y i) (e i) (hy i) (he i) (h2 i hi)
        (β i) (hβ i)
      exact ⟨x, h1, h2', fun _ => h3⟩
    · exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, fun h => absurd h hj⟩
  choose x hx1 hx2 hx3 using hx
  have hsum : X.Et p K + X.a' p K = X.d := by
    funext t
    have := (h41b p n' r K X hX hLa hk).2 t
    simp only [Pi.add_apply, Dat.a']
    omega
  have hDdeg : X.Dl p K O * u ∈ RRdeg O n' (r + K) X.d := by
    have h1 : X.Dl p K O ∈ Pol O (r + K) (X.Et p K) := by
      rw [← RRdeg_eq_Pol]; exact hDlHom p n' r K X O
    have h2 : u ∈ Pol O (r + K) (X.a' p K) := by
      rw [← RRdeg_eq_Pol]; exact hdeg
    have := hom_Pol_mul O h1 h2
    rw [hsum] at this
    rw [RRdeg_eq_Pol]
    exact this
  have hDne : X.Dl p K O * u ≠ 0 := mul_ne_zero (hDlNe p n' r K X O hX) hu0
  refine ⟨(∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) (x j)) * monomial l0 1,
    ⟨x, hx1, l0, hl0, rfl, ?_⟩, ?_⟩
  · exact hHom p n' r K X.F O x z β l0 X.d hx2 hβ (hDu ▸ hDdeg) (hDu ▸ hDne)
  · rw [hDu]
    simp only [map_mul, map_prod, map_phSeg]
    rw [Finset.prod_congr rfl fun i hi => by rw [← hx3 (i : ℤ) ⟨i, hi, rfl⟩]]

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.LamProdMonomial
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section LamAbs

variable {R : Type} [CommRing R] {F : Type} [Field F] {σ τ : Type} {J : ℕ}

theorem lam_prod_monomial {ι : Type} (s : Finset ι) (f : ι → τ →₀ ℕ) (a : ι → R) :
    ∏ i ∈ s, monomial (f i) (a i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi, ih, monomial_mul_monomial]

abbrev lam_ph (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (j : Fin J) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval fun v => (X (g j v) : MvPolynomial τ R) ^ e j v

theorem lam_expand (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (y : Fin J → MvPolynomial σ R) :
    ∏ j, lam_ph g e j (y j) = ∑ m ∈ Fintype.piFinset (fun j => (y j).support),
      monomial (∑ j, imgMon (g j) (e j) (m j)) (∏ j, AddMonoidAlgebra.coeff (y j) (m j)) := by
  classical
  have h : ∀ j, lam_ph g e j (y j) = ∑ m ∈ (y j).support, monomial (imgMon (g j) (e j) m) (AddMonoidAlgebra.coeff (y j) m) := by
    intro j
    conv_lhs => rw [(y j).as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => aeval_pow_monomial _ _ _ _
  rw [Finset.prod_congr rfl fun j _ => h j, Finset.prod_univ_sum]
  exact Finset.sum_congr rfl fun m _ => lam_prod_monomial _ _ _

theorem lam_coeff (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (l : τ →₀ ℕ) (S : Fin J → Set (σ →₀ ℕ))
    (hinj : ∀ m m' : Fin J → σ →₀ ℕ, (∀ j, m j ∈ S j) → (∀ j, m' j ∈ S j) →
      ∑ j, imgMon (g j) (e j) (m j) = ∑ j, imgMon (g j) (e j) (m' j) → m = m')
    (y : Fin J → MvPolynomial σ F) (hy : ∀ j, y j ∈ restrictSupport F (S j)) (s : Fin J → σ →₀ ℕ)
    (hs : ∀ j, s j ∈ S j) :
    AddMonoidAlgebra.coeff (monomial l (1 : F) * ∏ j, lam_ph g e j (y j)) (l + ∑ j, imgMon (g j) (e j) (s j)) =
      ∏ j, AddMonoidAlgebra.coeff (y j) (s j) := by
  classical
  rw [coeff_monomial_mul, one_mul, lam_expand, coeff_sum, Finset.sum_eq_single s]
  · rw [coeff_monomial, ite_eq_left rfl]
  · intro m hm hne
    rw [coeff_monomial, ite_eq_right]
    intro h
    apply hne
    refine hinj m s (fun j => ?_) hs h
    have := Fintype.mem_piFinset.mp hm j
    exact ((MvPolynomial.mem_restrictSupport_iff (R := F)).mp (hy j)) (Finset.mem_coe.mpr this)
  · intro hnot
    rw [coeff_monomial, ite_eq_left rfl]
    rw [Fintype.mem_piFinset] at hnot
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    exact Finset.prod_eq_zero (Finset.mem_univ j) (MvPolynomial.notMem_support_iff.mp hj)

theorem lam_dual {I : Type} {M : Type} [AddCommGroup M] [Module F M] (u : I → M)
    (hu : LinearIndependent F u) :
    ∃ ψ : M →ₗ[F] (I →₀ F), (∀ a, ψ (u a) a = 1) ∧ ∀ a b, b ≠ a → ψ (u a) b = 0 := by
  classical
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective (Finsupp.linearCombination F u)
    (LinearMap.ker_eq_bot.mpr hu)
  have h1 : ∀ a, ψ (u a) = Finsupp.single a 1 := by
    intro a
    have h2 : Finsupp.linearCombination F u (Finsupp.single a 1) = u a := by simp
    rw [← h2]
    exact congrArg (fun f => f (Finsupp.single a 1)) hψ
  refine ⟨ψ, fun a => by rw [h1]; simp, fun a b hb => by rw [h1, Finsupp.single_apply, ite_eq_right hb.symm]⟩

theorem lam_li_fixed (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (l : τ →₀ ℕ) (S : Fin J → Set (σ →₀ ℕ))
    (hinj : ∀ m m' : Fin J → σ →₀ ℕ, (∀ j, m j ∈ S j) → (∀ j, m' j ∈ S j) →
      ∑ j, imgMon (g j) (e j) (m j) = ∑ j, imgMon (g j) (e j) (m' j) → m = m')
    {I : Fin J → Type} [∀ j, Fintype (I j)] (u : ∀ j, I j → MvPolynomial σ F)
    (hu : ∀ j, LinearIndependent F (u j)) (hS : ∀ j i, u j i ∈ restrictSupport F (S j)) :
    LinearIndependent F fun a : ∀ j, I j => monomial l (1 : F) * ∏ j, lam_ph g e j (u j (a j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc b
  have hstar : ∀ s : Fin J → σ →₀ ℕ, ∑ a, c a * ∏ j, AddMonoidAlgebra.coeff (u j (a j)) (s j) = 0 := by
    intro s
    by_cases hs : ∀ j, s j ∈ S j
    · have h1 := congrArg (AddMonoidAlgebra.coeff · (l + ∑ j, imgMon (g j) (e j) (s j))) hc
      rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [coeff_smul, lam_coeff g e l S hinj (fun j => u j (a j)) (fun j => hS j (a j)) s hs, smul_eq_mul]
    · push Not at hs
      obtain ⟨j0, hj0⟩ := hs
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [Finset.prod_eq_zero (Finset.mem_univ j0) (li_coeff_zero (hS j0 (a j0)) hj0), mul_zero]
  choose ψ hψ using fun j => lam_dual (u j) (hu j)
  let supp : ∀ j, Finset (σ →₀ ℕ) := fun j => Finset.univ.biUnion fun a => (u j a).support
  let w : ∀ j, (σ →₀ ℕ) → F := fun j m => ψ j (monomial m 1) (b j)
  have hexp : ∀ j (a : I j), (ψ j (u j a)) (b j) = ∑ m ∈ supp j, AddMonoidAlgebra.coeff (u j a) m * w j m := by
    intro j a
    conv_lhs => rw [(u j a).as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply]
    have hsub : (u j a).support ⊆ supp j := fun m hm => Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hm⟩
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun m _ => ?_
      have : (monomial m (AddMonoidAlgebra.coeff (u j a) m) : MvPolynomial σ F) = AddMonoidAlgebra.coeff (u j a) m • monomial m (1 : F) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul]
    · intro m _ hm
      rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]
  have h1 : ∑ a, c a * ∏ j, (ψ j (u j (a j))) (b j) = c b := by
    rw [Finset.sum_eq_single b]
    · rw [Finset.prod_eq_one fun j _ => (hψ j).1 (b j), mul_one]
    · intro a _ hab
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hab
      rw [Finset.prod_eq_zero (Finset.mem_univ j) ((hψ j).2 (a j) (b j) hj.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : ∑ a, c a * ∏ j, (ψ j (u j (a j))) (b j) = 0 := by
    have e1 : ∀ a : ∀ j, I j, c a * ∏ j, (ψ j (u j (a j))) (b j) =
        ∑ s ∈ Fintype.piFinset supp, (c a * ∏ j, AddMonoidAlgebra.coeff (u j (a j)) (s j)) * ∏ j, w j (s j) := by
      intro a
      rw [Finset.prod_congr rfl fun j _ => hexp j (a j), Finset.prod_univ_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.prod_mul_distrib, mul_assoc]
    rw [Finset.sum_congr rfl fun a _ => e1 a, Finset.sum_comm]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← Finset.sum_mul, hstar s, zero_mul]
  rw [← h1, h2]

theorem lam_li_all {Φ : Type} (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (l : Φ → τ →₀ ℕ)
    (S : Φ → Fin J → Set (σ →₀ ℕ)) (I : Φ → Fin J → Type) [∀ f j, Fintype (I f j)]
    (u : ∀ f j, I f j → MvPolynomial σ F) (hu : ∀ f j, LinearIndependent F (u f j))
    (hS : ∀ f j i, u f j i ∈ restrictSupport F (S f j))
    (hinj : ∀ f f' (m m' : Fin J → σ →₀ ℕ), (∀ j, m j ∈ S f j) → (∀ j, m' j ∈ S f' j) →
      l f + ∑ j, imgMon (g j) (e j) (m j) = l f' + ∑ j, imgMon (g j) (e j) (m' j) → f = f' ∧ m = m') :
    LinearIndependent F fun x : (Σ f, ∀ j, I f j) =>
      monomial (l x.1) (1 : F) * ∏ j, lam_ph g e j (u x.1 j (x.2 j)) := by
  classical
  refine li_graded _ (fun x => x.1)
    (fun f => {n | ∃ m : Fin J → σ →₀ ℕ, (∀ j, m j ∈ S f j) ∧ n = l f + ∑ j, imgMon (g j) (e j) (m j)}) ?_ ?_ ?_
  · rintro k k' n ⟨m, hm, rfl⟩ ⟨m', hm', h⟩
    exact (hinj k k' m m' hm hm' h).1
  · intro x
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    have hn' : AddMonoidAlgebra.coeff (monomial (l x.1) (1 : F) * ∏ j, lam_ph g e j (u x.1 j (x.2 j))) n ≠ 0 :=
      MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hn)
    rw [coeff_monomial_mul'] at hn'
    split_ifs at hn' with hle
    · rw [one_mul, lam_expand, coeff_sum] at hn'
      obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn'
      rw [coeff_monomial] at hm0
      split_ifs at hm0 with heq
      · refine ⟨m, fun j => ?_, ?_⟩
        · exact ((MvPolynomial.mem_restrictSupport_iff (R := F)).mp (hS x.1 j (x.2 j)))
            (Finset.mem_coe.mpr (Fintype.mem_piFinset.mp hm j))
        · rw [heq]; exact (add_tsub_cancel_of_le hle).symm
      · exact absurd rfl hm0
    · exact absurd rfl hn'
  · intro k
    have hfix := lam_li_fixed g e (l k) (S k)
      (fun m m' hm hm' h => (hinj k k m m' hm hm' (by rw [h])).2) (u k) (hu k) (hS k)
    have hι : Function.Injective
        (fun x : {x : (Σ f, ∀ j, I f j) // x.1 = k} => (x.2 ▸ x.1.2 : ∀ j, I k j)) := by
      rintro ⟨⟨f, a⟩, h⟩ ⟨⟨f', a'⟩, h'⟩ hxx
      simp only at h h'
      subst h
      subst h'
      simp only at hxx
      rw [hxx]
    have hcomp := hfix.comp _ hι
    have heq : (fun x : {x : (Σ f, ∀ j, I f j) // x.1 = k} =>
        monomial (l x.1.1) (1 : F) * ∏ j, lam_ph g e j (u x.1.1 j (x.1.2 j))) =
        ((fun a : ∀ j, I k j => monomial (l k) (1 : F) * ∏ j, lam_ph g e j (u k j (a j))) ∘
          fun x : {x : (Σ f, ∀ j, I f j) // x.1 = k} => (x.2 ▸ x.1.2 : ∀ j, I k j)) := by
      funext x
      obtain ⟨⟨f, a⟩, h⟩ := x
      simp only at h
      subst h
      rfl
    rw [heq]
    exact hcomp

end LamAbs

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.RestCountOf
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def Pz (j x : ℤ) : ℕ := p ^ (X.F.dist j x + X.Rj p K j)


open Classical in
def laSet (t : Fin n') : Finset (Fin (r + K) → ℕ) :=
  (Fintype.piFinset fun _ : Fin (r + K) => Finset.range (X.a' p K t + 1)).filter fun v =>
    ∑ c, v c ≤ X.a' p K t ∧ ∀ j : ℤ, ∀ x ∈ X.toLate j, posOf n' x = t →
      (∀ c, v c < X.Pz p K j x) ∧ (∑ c, v c) % X.Pz p K j x = X.a' p K t % X.Pz p K j x

def LA : Finset (Fin n' → Fin (r + K) → ℕ) := Fintype.piFinset (X.laSet p K)

def nz (la : Fin n' → Fin (r + K) → ℕ) (j x : ℤ) : ℕ :=
  (X.a' p K (posOf n' x) - ∑ c, la (posOf n' x) c) / X.Pz p K j x


open Classical in
def EE (la : Fin n' → Fin (r + K) → ℕ) : Finset (Fin X.F.J → Fin r → ℕ) :=
  Fintype.piFinset fun j : Fin X.F.J => Fintype.piFinset fun i : Fin r =>
    (Finset.range (r * X.Qc p K (j.val : ℤ))).filter fun e =>
      e % X.Qc p K (j.val : ℤ) = X.nz p K la (j.val : ℤ) (X.F.fr (j.val : ℤ) i.val) % X.Qc p K (j.val : ℤ)


omit [NeZero n'] in
def eZ (e : Fin X.F.J → Fin r → ℕ) (j : ℤ) : Fin r → ℕ :=
  if h : 0 < X.F.J then e ⟨(j % (X.F.J : ℤ)).toNat % X.F.J, Nat.mod_lt _ h⟩ else 0


open Classical in
def bfam (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : ℤ) : ℤ → ℕ := fun x =>
  if x ∈ X.F.letters j then
    if X.F.IsW j x then
      ∑ i : Fin r, if x = X.F.fr (j - 1) i.val then
        (X.nz p K la (j - 1) x - X.eZ e (j - 1) i) / X.Qc p K (j - 1) else 0
    else if X.F.fr j 0 ≤ x then ∑ i : Fin r, if x = X.F.fr j i.val then X.eZ e j i else 0
    else X.nz p K la j x
  else 0


open Classical in
def setTau (j : ℤ) (b : ℤ → ℕ) (e : Fin r → ℕ) : ℤ → ℕ := fun x =>
  if X.F.fr j 0 ≤ x ∧ x ≤ X.F.fr j (r - 1) then ∑ i : Fin r, if x = X.F.fr j i.val then e i else 0 else b x

def AdmLL (j : ℤ) (b : ℤ → ℕ) : Prop :=
  ∀ x ∈ X.F.LLset j, (X.a' p K (posOf n' x) : ℝ) / (X.Pz p K j x : ℝ) - k (r := r) K < (b x : ℝ) ∧
    (b x : ℝ) ≤ (X.a' p K (posOf n' x) : ℝ) / (X.Pz p K j x : ℝ)

def segBound (j : ℤ) (b : ℤ → ℕ) : ℝ :=
  (1 - 1 / X.a ^ (X.Ns ^ 2)) *
    (∏ x ∈ X.F.LLset j, ((Nat.choose (b x + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
    (∏ i : Fin r, ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
    (((X.Qc p K j : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) ^ r


open Classical in
def SegOK [NeZero r] [NeZero K] (O : Type) [CommRing O] (j : ℤ) (G : (ℤ → ℕ) → ℝ) : Prop :=
  (∀ b, 0 ≤ G b) ∧
  (∀ b b' : ℤ → ℕ, (∀ x ∈ X.toLate j, b x = b' x) → G b = G b') ∧
  (∀ b : ℤ → ℕ, (∀ x, x ∉ X.F.letters j → b x = 0) →
    (∀ x ∈ X.F.letters j, X.F.IsW j x → X.Bw p K j x ≤ (b x : ℤ)) → X.AdmLL p K j b →
    G b ≤ (Module.finrank O (X.Mj p K O j b) : ℝ)) ∧
  (∀ b : ℤ → ℕ, X.AdmLL p K j b → ∀ ρ : Fin r → ℕ,
    X.segBound p K j b ≤ ∑ e ∈ Fintype.piFinset fun i : Fin r =>
      (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = ρ i % X.Qc p K j, G (X.setTau j b e))

end Dat

def RestLam (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∑ la ∈ X.LA p K, ∑ e ∈ X.EE p K la, ∏ j : Fin X.F.J,
        Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K la e (j.val : ℤ))) ≤
      Module.finrank (FF O) (X.LamBar p K O)

def RestSeg (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j : ℤ, ∃ G : (ℤ → ℕ) → ℝ, X.SegOK p K O j G

def RestPad (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ la ∈ X.LA p K, ∀ e ∈ X.EE p K la, ∀ j : ℤ,
      (∀ x ∈ X.F.letters j, X.F.IsW j x → X.Bw p K j x ≤ (X.bfam p K la e j x : ℤ)) ∧
      X.AdmLL p K j (X.bfam p K la e j)

def RestSum (C₀ Crk : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ G : ℤ → (ℤ → ℕ) → ℝ,
      (∀ j b, 0 ≤ G j b) →
      (∀ j, ∀ b b' : ℤ → ℕ, (∀ x ∈ X.toLate j, b x = b' x) → G j b = G j b') →
      (∀ j, ∀ b : ℤ → ℕ, X.AdmLL p K j b → ∀ ρ : Fin r → ℕ,
        X.segBound p K j b ≤ ∑ e ∈ Fintype.piFinset fun i : Fin r =>
          (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = ρ i % X.Qc p K j,
            G j (X.setTau j b e)) →
      ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) * X.bound K Crk ≤
        ∑ la ∈ X.LA p K, ∑ e ∈ X.EE p K la, ∏ j : Fin X.F.J, G (j.val : ℤ) (X.bfam p K la e (j.val : ℤ))

theorem restCount_of (C₀ Crk : ℝ) (hL : RestLam C₀) (hS : RestSeg C₀) (hP : RestPad C₀) (hSum : RestSum C₀ Crk) :
    RestCount C₀ Crk := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk
  choose G hG using hS p n' r K X O S hX hLa hk
  refine le_trans (hSum p n' r K X hX hLa hk G (fun j => (hG j).1) (fun j => (hG j).2.1) (fun j => (hG j).2.2.2)) ?_
  refine le_trans ?_ (Nat.cast_le.mpr (hL p n' r K X O S hX hLa hk))
  push_cast
  refine Finset.sum_le_sum fun la hla => Finset.sum_le_sum fun e he => ?_
  refine Finset.prod_le_prod₀ (fun j _ => (hG _).1 _) fun j _ => ?_
  obtain ⟨h1, h2⟩ := hP p n' r K X hX hLa hk la hla e he (j.val : ℤ)
  refine (hG _).2.2.1 _ ?_ h1 h2
  intro x hx
  simp [Dat.bfam, hx]

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

