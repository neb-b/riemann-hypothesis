module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NonemptyDvrSettingOfStandard
public import Lemmata.ComplementLifts.ComplLift

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Coarse
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)


open Classical in
def toLate (j : ℤ) : Finset ℤ := (X.F.letters j).filter fun x => ¬ X.F.IsW j x


open Classical in
def row (j x : ℤ) (i : Fin r) : ℤ :=
  let l := ((X.F.letters j).filter fun z => Even z ∧ z < x).sort (· ≤ ·)
  l.getD (l.length - r + i.val) 0

def detPl (O : Type) [CommRing O] (j x : ℤ) : MvPolynomial (ℤ × Fin r) O :=
  Matrix.det (Matrix.of fun a b : Fin r => (MvPolynomial.X (X.row j x a, b) : MvPolynomial (ℤ × Fin r) O))

def DlSeg (O : Type) [CommRing O] (j : ℤ) : MvPolynomial (ℤ × Fin r) O :=
  ∏ x ∈ X.toLate j, X.detPl O j x ^ X.sg p K j x

def Dl (O : Type) [CommRing O] : RRing O n' (r + K) :=
  ∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) (plEmb O r K (X.DlSeg p K O j))

def Et (t : Fin n') : ℕ :=
  ∑ j ∈ Finset.range X.F.J, ∑ x ∈ X.toLate j, X.sg p K j x *
    ∑ i : Fin r, if posOf n' (X.row j x i) = t then p ^ X.F.dist j (X.row j x i) else 0

def a' (t : Fin n') : ℕ := X.d t - X.Et p K t

def Rj (j : ℤ) : ℕ :=
  Nat.log p ⌊X.a / (8 * X.Y * k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0))⌋₊

def Qc (j : ℤ) : ℕ :=
  p ^ (X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + (X.Rj p K (j + 1) : ℤ) - (X.Rj p K j : ℤ)).toNat

def m0 : ℕ := (r + K) * X.Ns + 1

def phc (O : Type) [CommRing O] (j : ℤ) : SegRing O r K →ₐ[O] RRing O n' (r + K) :=
  aeval fun v => MvPolynomial.X (posOf n' v.1, v.2) ^ (p ^ (X.F.dist j v.1 + X.Rj p K j))

def IsCLabel (l : Fin n' × Fin (r + K) →₀ ℕ) : Prop :=
  ∀ j : ℤ, ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x → ∀ c, l (posOf n' x, c) < p ^ (X.F.dist j x + X.Rj p K j)

def resSet (j : ℤ) : Set (ℤ × Fin (r + K) →₀ ℕ) :=
  {m | ∀ i < r, ∀ c : Fin r, m (X.F.fr j i, Fin.castAdd K c) < X.Qc p K j}

def segDegSet (b : ℤ → ℕ) : Set (ℤ × Fin (r + K) →₀ ℕ) := {m | ∀ x, ∑ c : Fin (r + K), m (x, c) = b x}

def Bw (j y : ℤ) : ℤ :=
  ((X.a' p K (posOf n' y) / p ^ (X.F.dist j y + X.Rj p K j) : ℕ) : ℤ) - ((r + K + r + 1 : ℕ) : ℤ)


open Classical in
def thc (j : ℤ) (b : ℤ → ℕ) (x : ℤ) : ℝ :=
  (2 / 3) * (if X.F.IsW j (X.F.oldest j x) then ((X.Bw p K j (X.F.oldest j x) - (X.m0 K : ℤ) : ℤ) : ℝ)
    else (b (X.F.oldest j x) : ℝ))

def oc (j x : ℤ) : ℝ :=
  X.La * X.a / ((p : ℝ) * k (r := r) K * (p : ℝ) ^ (X.F.dist j x + X.Rj p K j)) +
    (if Even x then 4 * X.a * (p : ℝ) ^ (-((X.F.dist j (X.F.oldest j x) : ℤ) + (X.Rj p K j : ℤ))) else 0)

variable [NeZero r] [NeZero K]

def Mj (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ) : Submodule O (SegRing O r K) :=
  XX' O r K X.F j (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j) ⊓
    restrictSupport O (segDegSet (r := r) K b) ⊓ restrictSupport O (X.resSet p K j)

def lamGen (O : Type) [CommRing O] : Set (RRing O n' (r + K)) :=
  {u | ∃ (b : ℤ → ℤ → ℕ) (y : ℤ → SegRing O r K) (l : Fin n' × Fin (r + K) →₀ ℕ),
      (∀ j, y j ∈ X.Mj p K O j (b j)) ∧ X.IsCLabel p K l ∧
      u = (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y j)) * monomial l 1 ∧
      u ∈ RRdeg O n' (r + K) (X.a' p K)}

def LamBar (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Submodule (FF O) (RRing (FF O) n' (r + K)) :=
  Submodule.span (FF O) (MvPolynomial.map (IsLocalRing.residue O) '' X.lamGen p K O)

end Dat

def DiscriminantNonzeroModUniformiser : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], X.Hyp p K →
    MvPolynomial.map (IsLocalRing.residue O) (X.Dl p K O) ≠ 0

def GeneratorModuloUniformiser (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ u ∈ X.lamGen p K O, ∃ g ∈ X.gen p K O,
      MvPolynomial.map (IsLocalRing.residue O) (X.Dl p K O * u) = MvPolynomial.map (IsLocalRing.residue O) g

def RestCount (C₀ Crk : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) * X.bound K Crk ≤ (Module.finrank (FF O) (X.LamBar p K O) : ℝ)

theorem finite_restrictSupport (Fd : Type) [Field Fd] (σ : Type) (s : Set (σ →₀ ℕ)) (hs : s.Finite) :
    Module.Finite Fd (restrictSupport Fd s : Submodule Fd (MvPolynomial σ Fd)) := by
  have hle : (restrictSupport Fd s : Submodule Fd (MvPolynomial σ Fd)) ≤
      Submodule.span Fd ((fun m => (monomial m (1 : Fd) : MvPolynomial σ Fd)) '' s) := by
    intro P hP
    rw [MvPolynomial.mem_restrictSupport_iff] at hP
    rw [P.as_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have : (monomial m (AddMonoidAlgebra.coeff P m) : MvPolynomial σ Fd) = AddMonoidAlgebra.coeff P m • monomial m (1 : Fd) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hP (by exact_mod_cast hm), rfl⟩)
  have : Module.Finite Fd (Submodule.span Fd ((fun m => (monomial m (1 : Fd) : MvPolynomial σ Fd)) '' s)) :=
    FiniteDimensional.span_of_finite Fd (hs.image _)
  exact Submodule.finiteDimensional_of_le hle

theorem map_mem_restrictSupport {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {σ : Type} (s : Set (σ →₀ ℕ))
    {P : MvPolynomial σ R} (hP : P ∈ restrictSupport R s) : MvPolynomial.map f P ∈ restrictSupport S s := by
  rw [MvPolynomial.mem_restrictSupport_iff] at hP ⊢
  intro m hm
  exact hP (by exact_mod_cast MvPolynomial.support_map_subset f P (by exact_mod_cast hm))

theorem restRank_of (C₀ Crk : ℝ) (h1 : DiscriminantNonzeroModUniformiser) (h5 : GeneratorModuloUniformiser C₀) (hc : RestCount C₀ Crk) : RestRank C₀ Crk := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk
  refine le_trans (hc p n' r K X O S hX hLa hk) ?_
  have hD := h1 p n' r K X O hX
  have h45 := h5 p n' r K X O S hX hLa hk
  set res := MvPolynomial.map (σ := Fin n' × Fin (r + K)) (IsLocalRing.residue O) with hres
  let f : RRing (FF O) n' (r + K) →ₗ[FF O] RRing (FF O) n' (r + K) := LinearMap.mulLeft (FF O) (res (X.Dl p K O))
  have hf : Function.Injective f := by
    intro a b hab
    exact mul_left_cancel₀ hD hab
  have hmap : (X.LamBar p K O).map f ≤ X.NNbar p K O := by
    unfold Dat.LamBar
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨g, hg, hgu⟩ := h45 u hu
    have : f (res u) = res g := by
      rw [← hgu]; simp [f, hres]
    rw [this]
    exact Submodule.subset_span ⟨g, hg, rfl⟩
  have hfin : Module.Finite (FF O) (X.NNbar p K O) := by
    have := finite_restrictSupport (FF O) _ _ (degSet_finite n' (r + K) X.d)
    refine Submodule.finiteDimensional_of_le
      (S₂ := restrictSupport (FF O) {m : Fin n' × Fin (r + K) →₀ ℕ | ∀ t, ∑ c : Fin (r + K), m (t, c) = X.d t}) ?_
    unfold Dat.NNbar
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨x, -, l, -, -, h⟩ := hg
    exact map_mem_restrictSupport _ _ h
  have h1' : Module.finrank (FF O) ((X.LamBar p K O).map f) = Module.finrank (FF O) (X.LamBar p K O) :=
    (Submodule.equivMapOfInjective f hf (X.LamBar p K O)).finrank_eq.symm
  have h2 := Submodule.finrank_mono hmap
  rw [h1'] at h2
  exact_mod_cast h2

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SelIsComplRestrictSupport
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G

theorem sel_compl {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
    (N N' S : Submodule R M) (hNN' : IsCompl N N') [Module.Finite R N] (hS : S ≤ N)
    (hsat : ∀ (a : R) (x : M), a ≠ 0 → a • x ∈ S → x ∈ S) : ∃ T : Submodule R M, IsCompl S T := by
  exact Bl.ComplementLifts.goal1 N N' S hNN' hS hsat

theorem sel_isCompl_restrictSupport (R : Type*) [CommRing R] {σ : Type*} (s : Set (σ →₀ ℕ)) :
    IsCompl (restrictSupport R s) (restrictSupport R sᶜ) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [mem_restrictSupport_iff] at hx hx'
    rw [← support_eq_empty]
    ext m
    simp only [Finset.notMem_empty, iff_false]
    intro hm
    exact hx' (Finset.mem_coe.mpr hm) (hx (Finset.mem_coe.mpr hm))
  · rw [codisjoint_iff, restrictSupport_eq_span, restrictSupport_eq_span, ← Submodule.span_union, ← Set.image_union,
      Set.union_compl_self, ← restrictSupport_eq_span, restrictSupport_univ]

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}

theorem sel_red_sum {ι : Type} [Fintype ι] (c : ι → O) (v : ι → MvPolynomial σ O) :
    MvPolynomial.map (IsLocalRing.residue O) (∑ i, c i • v i) =
      ∑ i, IsLocalRing.residue O (c i) • MvPolynomial.map (IsLocalRing.residue O) (v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]

theorem sel_key {ι : Type} [Fintype ι] (v : ι → MvPolynomial σ O)
    (hv : LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (v i))
    {ϖ : O} (hϖ : Irreducible ϖ) (c : ι → O) (x : MvPolynomial σ O) (h : ∑ i, c i • v i = ϖ • x) :
    ∃ c' : ι → O, (∀ i, c i = ϖ * c' i) ∧ ∑ i, c' i • v i = x := by
  have hres : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
    exact hϖ.not_isUnit
  have h1 : ∑ i, IsLocalRing.residue O (c i) • MvPolynomial.map (IsLocalRing.residue O) (v i) = 0 := by
    rw [← sel_red_sum, h, smul_eq_C_mul, map_mul, map_C, hres, C_0, zero_mul]
  have h2 := Fintype.linearIndependent_iff.mp hv _ h1
  have h3 : ∀ i, ϖ ∣ c i := fun i => by
    have := (IsLocalRing.residue_eq_zero_iff _).mp (h2 i)
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
  choose c' hc' using h3
  refine ⟨c', hc', ?_⟩
  have h4 : ϖ • ∑ i, c' i • v i = ϖ • x := by
    rw [← h, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc' i, mul_smul]
  exact smul_right_injective _ hϖ.ne_zero h4

theorem sel_li {ι : Type} [Fintype ι] (v : ι → MvPolynomial σ O)
    (hv : LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (v i)) :
    LinearIndependent O v := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hP : ∀ n : ℕ, ∀ c : ι → O, ∑ i, c i • v i = 0 → ∀ i, ϖ ^ n ∣ c i := by
    intro n
    induction n with
    | zero => intro c _ i; simp
    | succ n ih =>
      intro c hc i
      obtain ⟨c', hc', hs⟩ := sel_key v hv hϖ c 0 (by rw [hc, smul_zero])
      obtain ⟨e, he⟩ := ih c' hs i
      exact ⟨e, by rw [hc' i, he, pow_succ]; ring⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_contra hne
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  obtain ⟨e, he⟩ := hP (n + 1) c hc i
  have h1 : ϖ ^ n * (u : O) = ϖ ^ n * (ϖ * e) := by
    rw [← mul_assoc, ← pow_succ, ← he, hu]; ring
  have h2 : (u : O) = ϖ * e := mul_left_cancel₀ (pow_ne_zero n hϖ.ne_zero) h1
  exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (h2 ▸ u.isUnit))

theorem sel_sat {ι : Type} [Fintype ι] (v : ι → MvPolynomial σ O)
    (hv : LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (v i))
    (a : O) (x : MvPolynomial σ O) (ha : a ≠ 0) (h : a • x ∈ Submodule.span O (Set.range v)) :
    x ∈ Submodule.span O (Set.range v) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have h1 : ϖ ^ n • x ∈ Submodule.span O (Set.range v) := by
    have := Submodule.smul_mem _ ((u⁻¹ : Oˣ) : O) h
    rwa [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
  clear h ha
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    apply ih
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp h1
    obtain ⟨c', -, hs⟩ := sel_key v hv hϖ c (ϖ ^ n • x) (by rw [hc, smul_smul, ← pow_succ'])
    exact (Submodule.mem_span_range_iff_exists_fun O).mpr ⟨c', hs⟩

end DVR

theorem restSel : RestSel := by
  intro O _ _ _ σ s hs G hG
  classical
  obtain ⟨b, hbG, hspan, hli⟩ := exists_linearIndependent (FF O) (MvPolynomial.map (IsLocalRing.residue O) '' G)

  have hsub : ∀ y ∈ MvPolynomial.map (IsLocalRing.residue O) '' G, y ∈ restrictSupport (FF O) s := by
    rintro y ⟨g, hg, rfl⟩
    have hg' := hG g hg
    rw [mem_restrictSupport_iff] at hg' ⊢
    exact fun m hm => hg' (Finset.mem_coe.mpr (support_map_subset _ _ hm))
  have : Finite ((fun m : σ →₀ ℕ => (monomial m (1 : FF O))) '' s) := (hs.image _).to_subtype
  have hfin : Finite b := by
    refine hli.finite_of_le_span_finite _ ((fun m : σ →₀ ℕ => (monomial m (1 : FF O))) '' s) ?_
    rintro y ⟨⟨y', hy'⟩, rfl⟩
    have := hsub y' (hbG hy')
    rwa [restrictSupport_eq_span] at this
  let : Fintype b := Fintype.ofFinite b

  have hpre : ∀ y : b, ∃ g ∈ G, MvPolynomial.map (IsLocalRing.residue O) g = (y : MvPolynomial σ (FF O)) :=
    fun y => hbG y.2
  choose v hvG hv using hpre
  have hli' : LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (v i) := by
    have : (fun i => MvPolynomial.map (IsLocalRing.residue O) (v i)) = ((↑) : b → MvPolynomial σ (FF O)) :=
      funext hv
    rw [this]; exact hli
  have hliO : LinearIndependent O v := sel_li v hli'
  have : Finite s := hs.to_subtype
  have : Module.Finite O (restrictSupport O s) := Module.Finite.of_basis (basisRestrictSupport O s)
  have hle : Submodule.span O (Set.range v) ≤ Submodule.span O G :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact hvG i)
  have hleN : Submodule.span O (Set.range v) ≤ restrictSupport O s :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hG _ (hvG i))
  refine ⟨Submodule.span O (Set.range v), hle, ?_, ⟨b, Module.Basis.span hliO, fun i => ?_⟩, ?_⟩
  · exact sel_compl _ _ _ (sel_isCompl_restrictSupport O s) hleN (fun a x ha h => sel_sat v hli' a x ha h)
  · rw [Module.Basis.span_apply]; exact hvG i
  · rw [finrank_span_eq_card hliO, ← hspan]
    have : Submodule.span (FF O) b = Submodule.span (FF O) (Set.range ((↑) : b → MvPolynomial σ (FF O))) := by
      rw [Subtype.range_coe]
    rw [this, finrank_span_eq_card hli]

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

