module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SatOfFixed
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace UpperTheory.V.Af

theorem hasFixed_of_sum {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G V) (hσ : GlobalTheory.PRep.IsSmooth σ) (ρ : Representation ℂ G W)
    (K : Subgroup G) (hK : IsCompact (K : Set G))
    (h : ⨆ f : {f : V →ₗ[ℂ] W // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 = ⊤) (hf : HasFixed ρ K) :
    HasFixed σ K := by
  classical
  open GlobalTheory.OrbitAvg in
  by_contra hn
  obtain ⟨x, hx0, hx⟩ := hf
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hfi : ∀ y, (stab σ K y).FiniteIndex := fun y => by
    have ho : IsOpen (stab σ K y : Set K) := (hσ y).preimage continuous_subtype_val
    haveI := (stab σ K y).quotient_finite_of_isOpen ho
    exact Subgroup.finiteIndex_of_finite_quotient
  have hz : ∀ y, avg σ K y = 0 := fun y => by
    by_contra h0
    exact hn ⟨_, h0, fun u hu => avg_invariant σ K (hfi y) ⟨u, hu⟩⟩
  have key : ∀ z ∈ (⊤ : Submodule ℂ W), (stab ρ K z).FiniteIndex ∧ avg ρ K z = 0 := fun z hz' => by
    rw [← h] at hz'
    refine Submodule.iSup_induction _ (motive := fun z => (stab ρ K z).FiniteIndex ∧ avg ρ K z = 0) hz' ?_ ?_ ?_
    · rintro ⟨f, hf⟩ _ ⟨y, rfl⟩
      haveI := hfi y
      have hle : stab σ K y ≤ stab ρ K (f y) := fun l hl => by
        rw [mem_stab] at hl ⊢
        rw [← hf, hl]
      refine ⟨Subgroup.finiteIndex_of_le hle, ?_⟩
      haveI := Fintype.ofFinite (K ⧸ stab σ K y)
      have := congrArg f (hz y)
      rw [avg_eq ρ K hle, ← map_zero f, ← this]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [avg, avgH, cv, finsum_eq_sum_of_fintype, map_smul, map_sum, hf]
    · have : stab ρ K (0 : W) = ⊤ := eq_top_iff.2 fun l _ => by rw [mem_stab, map_zero]
      have h1 : (stab ρ K (0 : W)).FiniteIndex := this ▸ inferInstance
      exact ⟨h1, avg_fixed ρ K h1 fun l _ => map_zero _⟩
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      exact ⟨Subgroup.finiteIndex_of_le (stab_le_add ρ K a b), by rw [avg_add ρ K ha hb, ha', hb', add_zero]⟩
  obtain ⟨h1, h2⟩ := key x trivial
  exact hx0 ((avg_fixed ρ K h1 hx).symm.trans h2)

variable {F : Type} [Field F] [NumberField F]

private def sInt (w : HeightOneSpectrum (𝓞 F)) : (w.adicCompletionIntegers F).toSubring →ₙ+* Ohat F where
  toFun x := ⟨sLoc F w x, Subring.mem_iInf.2 fun v => by
    classical
    change Pi.single (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) w (x : w.adicCompletion F) v ∈
      v.adicCompletionIntegers F
    by_cases hv : v = w
    · subst hv
      rw [Pi.single_eq_same]
      exact x.2
    · rw [Pi.single_eq_of_ne hv]
      exact zero_mem _⟩
  map_mul' x y := Subtype.ext (map_mul (sLoc F w) _ _)
  map_zero' := Subtype.ext (map_zero (sLoc F w))
  map_add' x y := Subtype.ext (map_add (sLoc F w) _ _)

private theorem sInt_natMul (w : HeightOneSpectrum (𝓞 F)) (M : ℕ) (x : (w.adicCompletionIntegers F).toSubring) :
    sInt w (M * x) = M * sInt w x := by
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul]

private theorem isUnit_nat (w : HeightOneSpectrum (𝓞 F)) {M : ℕ} (hM : (M : 𝓞 F) ∉ w.asIdeal) :
    IsUnit (M : (w.adicCompletionIntegers F).toSubring) := by
  have h1 : Valued.v (M : w.adicCompletion F) = 1 := by
    have : (M : w.adicCompletion F) = algebraMap F _ (algebraMap (𝓞 F) F M) := by simp
    rw [this]
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (algebraMap (𝓞 F) F M)
    refine h2.trans ?_
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hM
  have h0 : (M : w.adicCompletion F) ≠ 0 := fun h => by simp [h] at h1
  refine IsUnit.of_mul_eq_one ⟨(M : w.adicCompletion F)⁻¹, ?_⟩ (Subtype.ext ?_)
  · change Valued.v (M : w.adicCompletion F)⁻¹ ≤ 1
    rw [map_inv₀, h1, inv_one]
  · simpa using mul_inv_cancel₀ h0

theorem locGL_mem_KLev (n : ℕ) (w : HeightOneSpectrum (𝓞 F)) {M : ℕ} (hM : (M : 𝓞 F) ∉ w.asIdeal)
    {k : GL (Fin n) (w.adicCompletion F)} (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : locGL F n w k ∈ KLev F n M := by
  obtain ⟨k, rfl⟩ := hk
  refine ⟨cornerGL n (sInt w) k, map_cornerGL_of_zero _ _ (fun x => ?_) k, ?_⟩
  · obtain ⟨y, rfl⟩ := (isUnit_nat w hM).dvd (a := x)
    rw [sInt_natMul]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  · ext i j : 2
    change ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j : Af F) - sLoc F w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers F).toSubring) i j) + sLoc F w _ =
      (1 : Matrix (Fin n) (Fin n) (Af F)) i j - sLoc F w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion F)) i j) + sLoc F w _
    by_cases h : i = j
    · subst h
      simp only [Matrix.one_apply_eq]
      rfl
    · simp only [Matrix.one_apply_ne h]
      rfl

theorem sat_of_isotypic (hS : SatLoc) {n M : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (Af F)) V) (hρ : HasFixed ρ (KLev F n M)) (w : HeightOneSpectrum (𝓞 F))
    (hw : (M : 𝓞 F) ∉ w.asIdeal) (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (hi : LocIsotypic ρ w σ) :
    ∃ B, GlobalTheory.LFun.HasSatGL w (ρ.comp (locGL F n w)) B := by
  obtain ⟨h1, h2⟩ := hS F n w σ
  obtain ⟨x, hx0, hx⟩ := hρ
  have hK : IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GL (Fin n) (w.adicCompletion F))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F w)
  obtain ⟨B, hB⟩ := h1 (hasFixed_of_sum σ.ρ σ.smooth (ρ.comp (locGL F n w)) _ hK hi.2
    ⟨x, hx0, fun u hu => hx _ (locGL_mem_KLev n w hw hu)⟩)
  exact ⟨B, (h2 _ _ hi B).2 hB⟩

end UpperTheory.V.Af
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp

namespace UpperTheory.V.Af.Wd

def IsTri {k W ι : Type} [Field k] [AddCommGroup W] [Module k W] {n : ℕ} (T : ι → End k W) (d : ι → Fin n → k) : Prop :=
  ∃ b : Basis (Fin n) k W, ∀ a, (∀ i j, j < i → LinearMap.toMatrix b b (T a) i j = 0) ∧
    ∀ i, LinearMap.toMatrix b b (T a) i i = d a i

def ops {Γ R : Type} (N : R) (ρ : Γ → R) : Option Γ → R := fun a => a.elim N ρ

@[simp] theorem ops_none {Γ R : Type} (N : R) (ρ : Γ → R) : ops N ρ none = N := rfl

def cycL {l : ℕ} [Fact l.Prime] (L : FinExt l) : GQ l →* (↥L.1)ˣ :=
  (Units.map (algebraMap ℚ_[l] ↥L.1 : ℚ_[l] →* ↥L.1)).comp (Loc.PP l).χQ

def FrobPow {l : ℕ} [Fact l.Prime] (g : GQ l) (k : ℕ) : Prop :=
  ∀ c : ↥(MaximalUnramifiedExtension l), g (c : Om l) = (((frobUr l ^ k) c : ↥(MaximalUnramifiedExtension l)) : Om l)

def TriSnoc : Prop :=
  ∀ (k W' W W'' ι : Type) [Field k] [AddCommGroup W'] [Module k W'] [AddCommGroup W] [Module k W] [AddCommGroup W'']
    [Module k W''] (n : ℕ) (T' : ι → End k W') (T : ι → End k W) (T'' : ι → End k W'') (f : W' →ₗ[k] W) (p : W →ₗ[k] W''),
    Function.Injective f → Function.Surjective p → Function.Exact f p → finrank k W'' = 1 →
    (∀ a x, f (T' a x) = T a (f x)) → (∀ a x, p (T a x) = T'' a (p x)) → ∀ d : ι → Fin (n + 1) → k,
    IsTri T' (fun a i => d a (Fin.castSucc i)) → (∀ a y, T'' a y = d a (Fin.last n) • y) → IsTri T d

def TriInit : Prop :=
  ∀ (k W ι : Type) [Field k] [AddCommGroup W] [Module k W] (n : ℕ) (T : ι → End k W) (d : ι → Fin (n + 1) → k), IsTri T d →
    ∃ (S : Submodule k W) (hS : ∀ a, ∀ x ∈ S, T a x ∈ S) (p : W →ₗ[k] k), Function.Surjective p ∧ LinearMap.ker p = S ∧
      (∀ a x, p (T a x) = d a (Fin.last n) * p x) ∧ IsTri (fun a => (T a).restrict (hS a)) (fun a i => d a (Fin.castSucc i))

def TriMono : Prop :=
  ∀ (k W Γ : Type) [Field k] [AddCommGroup W] [Module k W] (n : ℕ) (N : End k W) (ρ : Γ → End k W) (c : Γ → k)
    (μ : Γ → Fin n → k), (∀ σ, ρ σ * N = c σ • (N * ρ σ)) → IsTri (ops N ρ) (ops 0 μ) → N ≠ 0 →
    ∃ i j, ∀ σ, μ σ i = c σ * μ σ j

def TriDiag : Prop :=
  ∀ (W I : Type) [AddCommGroup W] [Module ℂ W] [Group I] (n : ℕ) (ρ : I →* End ℂ W) (d : I → Fin n → ℂ),
    (Set.range ρ).Finite → IsTri (fun s => ρ s) d →
    ∃ b : Basis (Fin n) ℂ W, ∀ s, LinearMap.toMatrix b b (ρ s) = Matrix.diagonal (d s)

def LetterExact : Prop :=
  ∀ (LL U D' D D'' F : Type) [Field LL] [Field U] [AddCommGroup D'] [Module LL D'] [AddCommGroup D] [Module LL D]
    [AddCommGroup D''] [Module LL D''] [Field F] [Algebra LL F] (m' : U →+* End LL D') (m : U →+* End LL D)
    (m'' : U →+* End LL D'') (τ : U →+* F) (T : D' →ₗ[LL] D) (S : D →ₗ[LL] D'') (hT : ∀ c, T ∘ₗ m' c = m c ∘ₗ T)
    (hS : ∀ c, S ∘ₗ m c = m'' c ∘ₗ S), Function.Exact T S → Function.Surjective S →
    Function.Exact (letterLin m' m F τ T hT) (letterLin m m'' F τ S hS) ∧ Function.Surjective (letterLin m m'' F τ S hS)

def DLeft : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) (V' V V'' : Type)
    [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
    [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    [AddCommGroup V''] [Module ↥L.1 V''] [Module ℚ_[l] V''] [IsScalarTower ℚ_[l] ↥L.1 V'']
    (ρ' : Representation ↥L.1 ↥(GK K) V') (ρ : Representation ↥L.1 ↥(GK K) V) (ρ'' : Representation ↥L.1 ↥(GK K) V'')
    (f : V' →ₗ[↥L.1] V) (p : V →ₗ[↥L.1] V'') (hf : ∀ g v, f (ρ' g v) = ρ g (f v)) (hp : ∀ g v, p (ρ g v) = ρ'' g (p v)),
    Function.Injective f → Function.Exact f p →
    Function.Injective (dmap P hf) ∧ Function.Exact (dmap P hf) (dmap P hp)

def DRight : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (V' V V'' : Type)
    [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
    [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V]
    [AddCommGroup V''] [Module ↥L.1 V''] [Module ℚ_[l] V''] [IsScalarTower ℚ_[l] ↥L.1 V'']
    (ρ' : Representation ↥L.1 ↥(GK K) V') (ρ : Representation ↥L.1 ↥(GK K) V) (ρ'' : Representation ↥L.1 ↥(GK K) V'')
    (f : V' →ₗ[↥L.1] V) (p : V →ₗ[↥L.1] V'') (_ : ∀ g v, f (ρ' g v) = ρ g (f v)) (hp : ∀ g v, p (ρ g v) = ρ'' g (p v)),
    Function.Injective f → Function.Surjective p → Function.Exact f p → IsPst (Loc.PP l) ρ →
    IsPst (Loc.PP l) ρ' ∧ IsPst (Loc.PP l) ρ'' ∧ Function.Surjective (dmap (Loc.PP l) hp)

def WdExact : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ) (K L : FinExt l) (V' V V'' : Type)
    [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
    [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V]
    [AddCommGroup V''] [Module ↥L.1 V''] [Module ℚ_[l] V''] [IsScalarTower ℚ_[l] ↥L.1 V'']
    (ρ' : Representation ↥L.1 ↥(GK K) V') (ρ : Representation ↥L.1 ↥(GK K) V) (ρ'' : Representation ↥L.1 ↥(GK K) V'')
    (f : V' →ₗ[↥L.1] V) (p : V →ₗ[↥L.1] V'') (hf : ∀ g v, f (ρ' g v) = ρ g (f v)) (hp : ∀ g v, p (ρ g v) = ρ'' g (p v)),
    Function.Injective f → Function.Surjective p → Function.Exact f p → IsPst (Loc.PP l) ρ →
    IsPst (Loc.PP l) ρ' ∧ IsPst (Loc.PP l) ρ'' ∧ Function.Injective (wdLin (Loc.PP l) ι hf) ∧
      Function.Surjective (wdLin (Loc.PP l) ι hp) ∧ Function.Exact (wdLin (Loc.PP l) ι hf) (wdLin (Loc.PP l) ι hp)

def WdTri : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Om l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (L : FinExt l) (n : ℕ) (V : Type) [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) (κ : Fin n → ↥(GK Bw.Kw) →* (↥L.1)ˣ)
    (μ : ↥(Weil h) → Fin n → ℂ), IsTri (fun g => ρ g) (fun g i => (κ i g : ↥L.1)) →
    (∀ i (hi : IsPst (Loc.PP l) (Loc.chRep (κ i))) σ y,
      haveI := hi.finite; wdRho (Loc.PP l) ι Bw h hj (Loc.chRep (κ i)) σ y = μ σ i • y) →
    ∀ hV : IsPst (Loc.PP l) ρ,
      haveI := hV.finite; IsTri (ops (wdN (Loc.PP l) ι ρ) fun σ => wdRho (Loc.PP l) ι Bw h hj ρ σ) (ops 0 μ)

def Line : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (ι : Om l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (L : FinExt l) (V : Type) [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V), finrank ↥L.1 V = 1 → ∀ (hV : IsPst P ρ)
    (x : ↥(Dpst P ρ)), x ≠ 0 → ∀ c : ↥L.1, c ≠ 0 →
    (phiD P ρ ^ resDeg l w) x = (Dpst P ρ).module.toSMul.smul c x →
    ∀ (σ : ↥(Weil h)) (s : ↥L.1),
      actD P ρ (weilToGK Bw h σ) x = (Dpst P ρ).module.toSMul.smul s x → ∀ y,
      haveI := hV.finite; wdRho P ι Bw h hj ρ σ y = ι ((c ^ (-deg σ) * s : ↥L.1) : Om l) • y

def TiltFrob : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (y : OCb l) (m : ℕ), 0 < m → y ^ l ^ m = y → ∀ (g : GQ l) (k : ℕ), FrobPow g k →
    (Loc.AIP l).actT g y = y ^ l ^ k

def WittPer : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (r : ℕ) (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ℤ_[l]), Continuous M →
    (∀ g : ↥(GK K), (g : GQ l) ∈ Loc.Iq l → M g = 1) → ∃ W : Matrix (Fin r) (Fin r) (Loc.Bcr l), IsUnit W.det ∧
      (∀ g, (M g).map (fun z => algebraMap ℚ_[l] (Loc.Bcr l) (z : ℚ_[l])) * W.map ((Loc.PP l).actQ (g : GQ l)) = W) ∧
      ∀ (g : ↥(GK K)) (k : ℕ), FrobPow (g : GQ l) k →
        (M g).map (fun z => algebraMap ℚ_[l] (Loc.Bcr l) (z : ℚ_[l])) * W.map ((Loc.PP l).φB ^ k) = W

def IntBasis : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (V : Type) [AddCommGroup V]
    [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    (ρ : Representation ℚ_[l] Γ V), (∀ x, Continuous fun g => ρ g x) →
    ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] V) (M : Γ →* Matrix (Fin n) (Fin n) ℤ_[l]), Continuous M ∧
      ∀ g i j, ((M g i j : ℤ_[l]) : ℚ_[l]) = e.repr (ρ g (e j)) i

def UnrPer : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (η : ↥(GK K) →* (↥L.1)ˣ), Continuous (fun g => ((η g : ↥L.1) : Om l)) →
    (∀ g : ↥(GK K), (g : GQ l) ∈ Loc.Iq l → η g = 1) → ∃ u : ↥L.1 ⊗[ℚ_[l]] Bst (Loc.PP l), u ≠ 0 ∧
      (∀ g, stRep (Loc.PP l) (Loc.chRep η) g u = u) ∧
      ∀ (g : ↥(GK K)) (k : ℕ), FrobPow (g : GQ l) k → (η g : ↥L.1) • (phiV (Loc.PP l) ↥L.1 ↥L.1 ^ k) u = u

def TwistPer : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (κ χ η : ↥(GK K) →* (↥L.1)ˣ) (m : ℤ),
    (∀ g, κ g = cycL L (g : GQ l) ^ m * χ g * η g) → Continuous (fun g => ((η g : ↥L.1) : Om l)) →
    (∀ g : ↥(GK K), (g : GQ l) ∈ Loc.Iq l → η g = 1) → ∃ y : ↥L.1 ⊗[ℚ_[l]] Bst (Loc.PP l), y ≠ 0 ∧
      (∀ g, stRep (Loc.PP l) (Loc.chRep κ) g y = (χ g : ↥L.1) • y) ∧
      ∀ (g : ↥(GK K)) (k : ℕ), FrobPow (g : GQ l) k →
        ((η g : ↥L.1) * (l : ↥L.1) ^ (m * k)) • (phiV (Loc.PP l) ↥L.1 ↥L.1 ^ k) y = y

def BrFacts : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw →
    FrobPow (weilToGK Bw h (frob h) : GQ l) (resDeg l w) ∧
    (∀ (L : FinExt l) (s : ↥(Dec (F := F) A)), ((cycL L (Bw.e s : GQ l) : ↥L.1) : Om l) = (cycBar F Ω l s : Qbar l)) ∧
    ∀ M : ℕ, 1 ≤ M → ∃ K' : FinExt l, ∀ s : ↥(Dec (F := F) A), (Bw.e s : GQ l) ∈ GK K' →
      ∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ

def CharWD : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Om l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (L : FinExt l) (κ χ : ↥(GK Bw.Kw) →* (↥L.1)ˣ) (m : ℤ), Continuous (fun g => ((κ g : ↥L.1) : Om l)) →
    (∃ K' : FinExt l, ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ GK K' → χ g = 1) →
    (∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ Loc.Iq l → κ g = cycL L (g : GQ l) ^ m * χ g) →
    ∀ (hκ : IsPst (Loc.PP l) (Loc.chRep κ)) (σ : ↥(Weil h)) y,
      haveI := hκ.finite
      wdRho (Loc.PP l) ι Bw h hj (Loc.chRep κ) σ y = (((normV w : ℕ) : ℂ) ^ (m * deg σ) *
        ι (((κ (weilToGK Bw h σ) * cycL L (weilToGK Bw h σ : GQ l) ^ (-m) : (↥L.1)ˣ) : ↥L.1) : Om l)) • y

def WeilDense : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    DenseRange (Subgroup.inclusion (Weil_le_Dec h))

def CharEnd : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), w ∈ placesOver F l →
    ∀ (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (a : ℤ), Continuous (fun s => (ψ s : Qbar l)) →
    (∀ σ : ↥(Weil h), ι (ψ (Subgroup.inclusion (Weil_le_Dec h) σ) : Qbar l) = ((normV w : ℕ) : ℂ) ^ (a * deg σ)) →
    a = 0 ∧ ψ = 1

def FinVal : Prop :=
  ∀ (F Ω C : Type) [Field F] [Field Ω] [Algebra F Ω] [Group C] (M : ℕ), 1 ≤ M → ∀ χ : G F Ω →* C, KillsMu M χ →
    (Set.range χ).Finite

def Model : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l))
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ) (χ : Fin n → G F Ω →* (Qbar l)ˣ), (∀ i, (Set.range (χ i)).Finite) →
    IsFlagOn r (Dec (F := F) A) κ → IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
    ∃ (L : FinExt l) (ρ : Representation ↥L.1 ↥(GK Bw.Kw) (Fin n → ↥L.1)) (κL χL : Fin n → ↥(GK Bw.Kw) →* (↥L.1)ˣ),
      IsPst (Loc.PP l) ρ ∧ wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype) = wdPst (Loc.PP l) ι Bw h hj ρ ∧
      IsTri (fun g => ρ g) (fun g i => (κL i g : ↥L.1)) ∧
      (∀ i s, ((κL i (Bw.e s) : ↥L.1) : Om l) = (κ i s : Qbar l)) ∧
      ∀ i (s : ↥(Dec (F := F) A)), ((χL i (Bw.e s) : ↥L.1) : Om l) = (χ i s : Qbar l)

end UpperTheory.V.Af.Wd
end
end

