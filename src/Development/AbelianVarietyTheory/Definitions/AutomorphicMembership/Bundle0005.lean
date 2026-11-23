module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EisGEqZeroOfInfinite
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField

namespace GlobalTheory.Mem.Per.Model

theorem eisG_map (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) (k : ℕ) :
    eisG (Λ.map (AddMonoidHom.mulLeft δ)) k = (δ ^ (2 * k))⁻¹ * eisG Λ k := by
  unfold eisG
  rw [← tsum_mul_left]
  let f : {w : ℂ // w ∈ Λ ∧ w ≠ 0} → {w : ℂ // w ∈ Λ.map (AddMonoidHom.mulLeft δ) ∧ w ≠ 0} :=
    fun w => ⟨δ * w.1, ⟨w.1, w.2.1, rfl⟩, mul_ne_zero hδ w.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Subtype.ext (mul_left_cancel₀ hδ (congrArg Subtype.val h))
    · rintro ⟨w, ⟨v, hv, rfl⟩, h0⟩
      refine ⟨⟨v, hv, ?_⟩, rfl⟩
      rintro rfl
      simp at h0
  rw [← (Equiv.ofBijective f hf).tsum_eq]
  refine tsum_congr fun w => ?_
  simp [f, mul_pow, mul_comm]

theorem discr_map (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) :
    TaylorLogMetric.discr (Λ.map (AddMonoidHom.mulLeft δ)) = (δ ^ 12)⁻¹ * TaylorLogMetric.discr Λ := by
  unfold TaylorLogMetric.discr g2 g3
  rw [eisG_map _ _ hδ, eisG_map _ _ hδ]
  field_simp
  ring

theorem jLat_map (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) :
    jLat (Λ.map (AddMonoidHom.mulLeft δ)) = jLat Λ := by
  unfold jLat
  rw [discr_map _ _ hδ]
  unfold g2
  rw [eisG_map _ _ hδ]
  by_cases h : TaylorLogMetric.discr Λ = 0
  · simp [h]
  · field_simp
    ring

variable {LL : Type} [Field LL] [NumberField LL]

variable {R : Ranks} (H : Host R)

theorem ellLat_ne_bot (embE : H.E →+* LL) (g : R.GG) : ellLat H embE g ≠ ⊥ := by
  have hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  have hb : H.𝔟 ≠ ⊥ := by
    intro h0
    apply hd
    have := H.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at this
    exact this
  have hA : H.AA0 ≠ 0 := by
    unfold Host.AA0
    exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb)
  obtain ⟨a, ha0, ha⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hA |>.imp fun a h => h
  obtain ⟨b, hb1, hb0⟩ := (Submodule.ne_bot_iff _).1 hd
  intro h
  have : embE (H.sigmaOf g ((a : H.E) * (b : H.E))) ∈ ellLat H embE g :=
    Submodule.subset_span ⟨_, ha, b, hb1, rfl⟩
  rw [h, Submodule.mem_bot] at this
  simp [ha0, hb0] at this

theorem ne_zero_of_isGen {embE : H.E →+* LL} {g : R.GG} {x : LL} (h : IsGen H embE g x) : x ≠ 0 := by
  rintro rfl
  apply ellLat_ne_bot H embE g
  rw [← h]; simp

theorem gen_spec {emb : LL →+* ℂ} {embE : H.E →+* LL} (h : FieldOK H emb embE) (g) :
    IsGen H embE g (gen H embE g) := Classical.epsilon_spec (h.2 g)

theorem area_pos_of_isConjLat {emb s : LL →+* ℂ} {Λ Λ' : AddSubgroup ℂ} (h : IsConjLat emb s Λ Λ') :
    (∃ L : PeriodPair, ∀ z, z ∈ Λ' ↔ z ∈ L.lattice) ∧ 0 < area Λ' := by
  obtain ⟨L, hL⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_discr_ne_zero (Λ := Λ') (by rw [h.1]; exact one_ne_zero)
  exact ⟨⟨L, hL⟩, (GlobalTheory.PlaneLattice.area_pos_and_selfDual L Λ' hL).1⟩

theorem exists_isConjLat (emb s : LL →+* ℂ) (Λ : AddSubgroup ℂ) (ha : ∃ a : LL, emb a = jLat Λ) :
    ∃ Λ', IsConjLat emb s Λ Λ' := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (s a / 1728) (n := 3) (by norm_num)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((s a / 1728 - 1) / 27) (n := 2) (by norm_num)
  have h1 : x ^ 3 - 27 * y ^ 2 = 1 := by rw [hx, hy]; ring
  obtain ⟨L, h2, h3⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants (a := x) (b := y)
    (by rw [h1]; exact one_ne_zero)
  have hd := GlobalTheory.LatticeInvariants.invariants_dictionary L L.lattice.toAddSubgroup (fun _ => Iff.rfl)
  have hD : TaylorLogMetric.discr L.lattice.toAddSubgroup = 1 := by
    unfold TaylorLogMetric.discr; rw [hd.1, hd.2.1, h2, h3, h1]
  refine ⟨L.lattice.toAddSubgroup, hD, a, ha, ?_⟩
  unfold jLat
  rw [hD, hd.1, h2, hx]; ring

theorem conjLat_spec {emb : LL →+* ℂ} {embE : H.E →+* LL} (h : FieldOK H emb embE) (s : LL →+* ℂ) :
    IsConjLat emb s (baseLat H) (conjLat H emb s) :=
  Classical.epsilon_spec (exists_isConjLat emb s _ h.1)

theorem om_eq {emb : LL →+* ℂ} {embE : H.E →+* LL} (h : FieldOK H emb embE) {I : Type}
    (e : I ≃ R.Psi) (τ : I) (s : LL →+* ℂ) :
    (trueGx H emb embE e).Om τ s = area (conjLat H emb s) / (Real.pi * ‖s (gen H embE (e τ).1)‖ ^ 2) := by
  have h1 := (area_pos_of_isConjLat (conjLat_spec H h s)).2
  have h2 : s (gen H embE (e τ).1) ≠ 0 := (map_ne_zero s).2 (ne_zero_of_isGen H (gen_spec H h _))
  have h3 : 0 < omAt H emb s (gen H embE (e τ).1) := by
    unfold omAt
    have := norm_pos_iff.2 h2
    have := Real.pi_pos
    positivity
  show posOr1 _ = _
  unfold posOr1
  rw [if_pos h3]; rfl

end GlobalTheory.Mem.Per.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
section
noncomputable section

namespace GlobalTheory.Mem.Col2.Th

open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

variable {R : Ranks} (H : Host R) {ι : Type} [Fintype ι] (emb : ι → H.E →+* ℂ)

abbrev Lt (N : ℕ) : Type := Submodule (𝓞 H.E) (Fin N → H.E)

abbrev VC (ι : Type) (N N' : ℕ) : Type := ι → Fin N' → Fin N → ℂ

def lamOf (cc : Ideal (𝓞 H.K)) (δ : ℂ) : AddSubgroup ℂ :=
  AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * H.φ₀ (((c : H.K) : H.E))}

def IsDiscriminantTwelfthRootOfIdealLattice (cc : Ideal (𝓞 H.K)) (δ : ℂ) : Prop := δ ^ 12 = TaylorLogMetric.discr (lamOf H cc 1)

def IsTwoTorsionPointUnkilled (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  2 * t ∈ Λ ∧ ((1 + Complex.I * (Real.sqrt H.d : ℂ)) / 2) * t ∉ Λ ∧
    ((1 - Complex.I * (Real.sqrt H.d : ℂ)) / 2) * t ∉ Λ

def stdL (N : ℕ) : Lt H N := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 H.E) H.E)

def homL {N N' : ℕ} (L : Lt H N) (L' : Lt H N') : Submodule (𝓞 H.E) (Matrix (Fin N') (Fin N) H.E) :=
  Submodule.span (𝓞 H.E) {A | ∀ x ∈ L, A.mulVec x ∈ L'}

def YYl {N N' : ℕ} (L : Lt H N) (L' : Lt H N') : Submodule (𝓞 H.E) (Matrix (Fin N') (Fin N) H.E) :=
  Submodule.span (𝓞 H.E) {B | ∃ a ∈ (H.AA0 : Submodule (𝓞 H.E) H.E), ∃ A ∈ homL H L L', B = a • A}

def La (Λ : AddSubgroup ℂ) {N N' : ℕ} (L : Lt H N) (L' : Lt H N') : AddSubgroup (VC ι N N') :=
  AddSubgroup.closure {z | ∃ w ∈ Λ, ∃ A ∈ YYl H L L', z = w • (fun τ i j => emb τ (A i j) : VC ι N N')}

def Hf (Λ : AddSubgroup ℂ) {N N' : ℕ} (z w : VC ι N N') : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (TaylorLogMetric.area Λ : ℂ)

def al (Λ : AddSubgroup ℂ) {N N' : ℕ} (x : VC ι N N') : ℂ :=
  (-1 : ℂ) ^ (round (Real.sqrt H.d / 2 * (Hf Λ x x).re))

def U (Λ : AddSubgroup ℂ) {N N' : ℕ} (x : VC ι N N') (G : VC ι N N' → ℂ) : VC ι N N' → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * Hf Λ z x - (Real.pi : ℂ) * Hf Λ x x / 2)

def Iop (Λ : AddSubgroup ℂ) {N N' : ℕ} (La₁ La₂ : AddSubgroup (VC ι N N')) (G : VC ι N N' → ℂ) : VC ι N N' → ℂ :=
  fun z => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
    ∑ᶠ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      al H Λ ((Quotient.out q : La₂) : VC ι N N') * U Λ ((Quotient.out q : La₂) : VC ι N N') G z

def detId {N : ℕ} (L L' : Lt H N) : Submodule (𝓞 H.E) H.E :=
  Submodule.span (𝓞 H.E) {x | ∃ A : Matrix (Fin N) (Fin N) H.E, (∀ v ∈ L, A.mulVec v ∈ L') ∧ x = A.det}

def lamMM (Λ : AddSubgroup ℂ) : AddSubgroup (ι → ℂ) :=
  AddSubgroup.closure {z | ∃ w ∈ Λ, ∃ a ∈ H.AA0, z = fun τ => w * emb τ a}

def mmM (M : IntermediateField ℚ ℂ) [NumberField M] : Submodule (𝓞 M) (ι → M) :=
  Submodule.span (𝓞 M) {v | ∃ a ∈ (H.AA0 : Submodule (𝓞 H.E) H.E), v = fun τ => TaylorLogMetric.liftM M (emb τ a)}

def ellT (M : IntermediateField ℚ ℂ) [NumberField M] (τ : ι) : Submodule (𝓞 M) M :=
  (mmM H emb M).comap (LinearMap.single (𝓞 M) (fun _ : ι => (M : Type)) τ)

def IsDgen (cD : ι → ℂ) : Prop :=
  ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M), (∀ τ x, emb τ x ∈ M) ∧ ∀ τ, ∃ s : M, (s : ℂ) = cD τ ∧
    ellT H emb M τ = Submodule.span (𝓞 M) {s}

def SplitK (p : ℕ) : Prop := p = 2 ∨ jacobiSym (-(H.d : ℤ)) p = 1


variable (ι) in
abbrev IsoK : Type := IsoKG H.K H.E H.conj ι


variable {H} in
def AtP (γ : IsoK H ι) (p : ℕ) : Prop :=
  (∀ x : Fin 4 → H.E, (∀ a, x a ∈ H.AA0) → ∃ s : ℕ, Nat.Coprime s p ∧
    ∀ w, (s : H.K) * γ.g x w ∈ (algebraMap (𝓞 H.K) H.K).range) ∧
  ∀ v : Fin 4 × ι → H.K, (∀ w, v w ∈ (algebraMap (𝓞 H.K) H.K).range) →
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ a, (s : H.E) * γ.g.symm v a ∈ H.AA0


variable {H} in
def detRel (γ γ₀ : IsoK H ι) : H.K :=
  LinearMap.det ((γ₀.g.symm.trans γ.g : (Fin 4 × ι → H.K) ≃ₗ[H.K] _) : (Fin 4 × ι → H.K) →ₗ[H.K] (Fin 4 × ι → H.K))


variable {H} in
structure KapIn (γ₀ : IsoK H ι) where
  pp : ℕ → IsDedekindDomain.HeightOneSpectrum (𝓞 H.K)
  pp_over : ∀ p, p.Prime → SplitK H p → ((p : ℕ) : 𝓞 H.K) ∈ (pp p).asIdeal
  pi : ℕ → 𝓞 H.K
  pi_gen : ∀ p, p.Prime → SplitK H p → (pp p).asIdeal ^ classNumber H.K = Ideal.span {pi p}
  gaP : ℕ → IsoK H ι
  gaP_at : ∀ p, p.Prime → SplitK H p → AtP (gaP p) p
  rt : ℕ → ℂ
  rt_pow : ∀ p, p.Prime → SplitK H p → rt p ^ (2 * classNumber H.K)
    = H.φ₀ (((pi p : 𝓞 H.K) : H.K) : H.E) / H.φ₀ (H.conj (((pi p : 𝓞 H.K) : H.K) : H.E))


variable {H} in
def KapIn.yP {γ₀ : IsoK H ι} (k : KapIn γ₀) (p : ℕ) : ℤ :=
  -WithZero.log ((k.pp p).valuation H.K (detRel (k.gaP p) γ₀))


variable {H} in
def KapIn.kappa {γ₀ : IsoK H ι} (k : KapIn γ₀) : ℂ :=
  ∏ᶠ p : {p : ℕ // p.Prime ∧ SplitK H p}, k.rt p ^ (-(k.yP p))

structure VacIn (cc : Ideal (𝓞 H.K)) (δ : ℂ) where
  L : PeriodPair
  lat : L.lattice.toAddSubgroup = lamOf H cc δ
  ω₀ : ℂ
  t0 : IsTwoTorsionPointUnkilled H (lamOf H cc δ) (ω₀ / 2)
  γ₀ : IsoK H ι
  gC : (Fin 4 × ι → ℂ) ≃ₗ[ℂ] (Fin 4 × ι → ℂ)
  gC_spec : ∀ x : Fin 4 → H.E, gC (fun w => emb w.2 (x w.1)) = fun w => H.φ₀ ((γ₀.g x w : H.K) : H.E)
  kc : KapIn γ₀

def chiFac (χ : Submodule (𝓞 H.E) H.E → ℂ) (N N' : ℕ) (L : Lt H N) (L' : Lt H N') : ℂ :=
  χ (detId H (stdL H N) L) ^ (((N' / 2 : ℕ) : ℤ)) * χ (detId H (stdL H N') L') ^ (-((N / 2 : ℕ) : ℤ))

def perAA (cc : Ideal (𝓞 H.K)) : Submodule (𝓞 H.E) H.E :=
  Submodule.span (𝓞 H.E) {r | ∃ c ∈ cc, ∃ t ∈ H.AA0, r = (((c : 𝓞 H.K) : H.K) : H.E) * t}

namespace VacIn

variable {H emb} {cc : Ideal (𝓞 H.K)} {δ : ℂ} (V : VacIn H emb cc δ)

def thMM : (ι → ℂ) → ℂ := thM V.L V.ω₀ (Real.sqrt H.d / 2) (lamMM H emb (lamOf H cc δ)) V.gC V.kc.kappa

def thZero (N N' : ℕ) : VC ι N N' → ℂ := tensPow V.thMM N N'

def thHalf (N N' : ℕ) (L : Lt H N) : VC ι N N' → ℂ :=
  Iop H (lamOf H cc δ) (La H emb (lamOf H cc δ) (stdL H N) (stdL H N')) (La H emb (lamOf H cc δ) L (stdL H N')) (V.thZero N N')

def thMoved (N N' : ℕ) (L : Lt H N) (L' : Lt H N') : VC ι N N' → ℂ :=
  Iop H (lamOf H cc δ) (La H emb (lamOf H cc δ) L (stdL H N')) (La H emb (lamOf H cc δ) L L') (V.thHalf N N' L)

def eNat (χ : Submodule (𝓞 H.E) H.E → ℂ) (N N' : ℕ) (L : Lt H N) (L' : Lt H N') : VC ι N N' → ℂ :=
  fun z => chiFac H χ N N' L L' * V.thMoved N N' L L' z

end VacIn

section Record

variable (D : D7)

theorem isDiscriminantTwelfthRoot_host_iff (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : IsDiscriminantTwelfthRootOfIdealLattice D.host cc δ ↔ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ := Iff.rfl

variable {D} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def KapIn.toRec {γ₀ : IsoK D.host D.what₂.Tau} (k : KapIn γ₀) : KapChoice (D := D) γ₀ :=
  ⟨k.pp, k.pp_over, k.pi, k.pi_gen, k.gaP, k.gaP_at, k.rt, k.rt_pow⟩

def VacIn.toRec (V : VacIn D.host (TaylorLogMetric.embT D) cc δ) : Formalism.L2.Ker.Base D cc δ :=
  ⟨V.L, V.lat, V.ω₀, V.t0, V.γ₀, V.gC, V.gC_spec, V.kc.toRec⟩

end Record

theorem perAA_top : perAA H ⊤ = (H.AA0 : Submodule (𝓞 H.E) H.E) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, -, t, ht, rfl⟩
    exact (H.AA0 : Submodule (𝓞 H.E) H.E).smul_mem (algebraMap (𝓞 H.K) (𝓞 H.E) c) ht
  · intro t ht
    exact Submodule.subset_span ⟨1, trivial, t, ht, by simp⟩

end GlobalTheory.Mem.Col2.Th

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Retie
section
noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory.Mem

def retie (D : D7) : D7 :=
  letI := D.host.cmStar
  { D with
    vol := fun W => Vol.trueVol D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W
    vol_pos := fun W => Vol.trueVol_pos D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W
    dsig := fun τ => Per.posOr1 (Vol.trueDsig D.R (D.hc τ))
    dsig_pos := fun _ => Per.posOr1_pos _
    s := { D.s with cdScale := Vol.trueScale D.cd, cdScale_pos := Vol.trueScale_pos D.cd }
    gx := Per.trueGx D.host D.what₂.embLL D.embE D.eTau }

end GlobalTheory.Mem
end
end

