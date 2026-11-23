module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0020
public import Formalism.SharpRestriction.LevelLetterCocycles.T2SpaceLatticeVOfGoodSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.ZlWCbInjective
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0021

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.EqZeroOfMemSum
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.Hodge

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Comp

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mulVdR_of_mem {τ : K →ₐ[Qp] LL} {y : V ⊗[Qp] BdR} (hy : y ∈ DdRE PD ρ τ) (c : K) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c y = τ c • y := by
  have h := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hy).2 c
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h
  exact h

theorem eq_zero_of_mem_sum (τ : K →ₐ[Qp] LL) :
    ∀ (s : Finset (K →ₐ[Qp] LL)), τ ∉ s → ∀ y ∈ DdRE PD ρ τ,
      y ∈ ⨆ τ' ∈ s, DdRE PD ρ τ' → y = 0 := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ y _ hy
    simpa using hy
  | insert a s ha ih =>
    intro hτ y hyτ hy
    have haτ : a ≠ τ := fun h => hτ (h ▸ Finset.mem_insert_self a s)
    have hτs : τ ∉ s := fun h => hτ (Finset.mem_insert_of_mem h)
    obtain ⟨c, hc⟩ : ∃ c : K, τ c ≠ a c := by
      by_contra h
      push_neg at h
      exact haτ (AlgHom.ext fun c => (h c).symm)

    let φ : Module.End LL (V ⊗[Qp] BdR) :=
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c - a c • LinearMap.id
    have hφ : ∀ τ', ∀ x ∈ DdRE PD ρ τ', φ x = (τ' c - a c) • x := by
      intro τ' x hx
      simp only [φ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        mulVdR_of_mem PD ρ hx c, sub_smul]
    have hW : ∀ x ∈ ⨆ τ' ∈ s, DdRE PD ρ τ', φ x ∈ ⨆ τ' ∈ s, DdRE PD ρ τ' := by
      intro x hx
      have hle : (⨆ τ' ∈ s, DdRE PD ρ τ') ≤ (⨆ τ' ∈ s, DdRE PD ρ τ').comap φ := by
        refine iSup₂_le fun τ' hτ' => fun z hz => ?_
        rw [Submodule.mem_comap, hφ τ' z hz]
        exact Submodule.smul_mem _ _ ((le_iSup₂ (f := fun τ' _ => DdRE PD ρ τ') τ' hτ') hz)
      exact hle hx
    rw [Finset.iSup_insert, Submodule.mem_sup] at hy
    obtain ⟨ya, hya, z, hz, hyz⟩ := hy
    have h1 : φ y ∈ ⨆ τ' ∈ s, DdRE PD ρ τ' := by
      rw [← hyz, map_add (f := _), hφ a ya hya, sub_self, zero_smul, zero_add]
      exact hW z hz
    rw [hφ τ y hyτ] at h1
    have h2 := ih hτs _ (Submodule.smul_mem _ _ hyτ) h1
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc)

theorem mem_of_mem_filC (τ : K →ₐ[Qp] LL) (F : Submodule LL (V ⊗[Qp] BdR)) (hF : F ≤ DdRE PD ρ τ)
    {x : V ⊗[Qp] BdR} (hx : x ∈ DdRE PD ρ τ)
    (h : x ∈ F ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD ρ τ') : x ∈ F := by
  classical
  obtain ⟨f, hf, z, hz, hfz⟩ := Submodule.mem_sup.mp h
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hz
  have hle : (⨆ τ' ∈ s, ⨆ (_ : τ' ≠ τ), DdRE PD ρ τ') ≤ ⨆ τ' ∈ s.filter (· ≠ τ), DdRE PD ρ τ' := by
    refine iSup₂_le fun τ' hτ' => iSup_le fun hne => ?_
    exact le_iSup₂ (f := fun τ' _ => DdRE PD ρ τ') τ' (Finset.mem_filter.mpr ⟨hτ', hne⟩)
  have hzτ : z ∈ DdRE PD ρ τ := by
    have e : z = x - f := by rw [← hfz]; abel
    rw [e]
    exact Submodule.sub_mem _ hx (hF hf)
  have hz0 := eq_zero_of_mem_sum PD ρ τ (s.filter (· ≠ τ)) (by simp) z hzτ (hle hs)
  rw [← hfz, hz0, add_zero]
  exact hf

theorem fildR_eq_bot (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] (b : ℤ)
    (hj : JumpsInV PD ρ τ (Set.Iic (-b))) : ∀ a : ℤ, -b < a → FildR PD ρ τ a = ⊥ := by
  intro a ha
  obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (PD := PD) (ρ := ρ) τ
  have hstep : ∀ c : ℤ, -b < c → FildR PD ρ τ c = FildR PD ρ τ (c + 1) := by
    intro c hc
    by_contra h
    have h2 := hj c (fun h' => h h'.symm)
    exact absurd (Set.mem_Iic.1 h2) (not_le.2 hc)
  have hk : ∀ k : ℕ, FildR PD ρ τ a = FildR PD ρ τ (a + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, hstep (a + k) (by omega)]
      congr 1
      push_cast
      ring
  rw [hk (hi - a).toNat]
  exact hhi _ (by omega)

end Comp

end Formalism.MainNotions.RamifiedCoefficientChains.S9.Hodge
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ExtDataOneMapSmulO
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LiftingTheory Formalism.MainNotions.CrystallineLiftingInputs

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def extDataOne_Rel (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ) (a N : ℕ)
    (y z : W.DD T) (μ ν : ZMod n → W.DD T) : Prop :=
  ∀ i : ZMod n, DL W T i (μ i) ∧ DL W T i (ν i) ∧
    InPN W T 1 (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • z) + (W.γ T (μ i) - μ i)) ∧
    qp W ^ Mi i • (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y) + W.φD T (μ (i - 1)) - μ i) ∈ W.N T ∧
    (∃ s : ℕ, ((PD.p : ℕ) : O) ^ s • (qp W ^ hi i •
      (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y) + W.φD T (μ (i - 1)) - μ i)) ∈
        pullJ W T (i - 1) 1) ∧
    ((PD.p : ℕ) : O) ^ N • ν i - qp W ^ a • μ i ∈ W.N T

theorem extDataOne_π₀_cancel (W : LocWach PD LL O v n) (R : lifta_Ring W) {T : LocLat G Qp LL O}
    (x : W.DD T) (h : W.π₀ • x = 0) : x = 0 := by
  apply (liftb_unit_bij W T W.π₀ R.πU).1
  change W.π₀ • x = W.π₀ • (0 : W.DD T)
  rw [smul_zero]
  exact h

theorem extDataOne_Qqp (W : LocWach PD LL O v n) (R : lifta_Ring W) (hs : W.s = 1) {T : LocLat G Qp LL O}
    (S : Submodule (LetA O n) (W.DD T)) (M : ℕ) (x : W.DD T) (h : W.Q ^ M • x ∈ S) : qp W ^ M • x ∈ S := by
  obtain ⟨w, hw⟩ := R.qq
  rw [lifta_Q_eq W hs, hw, mul_pow, mul_smul] at h
  have h' := S.smul_mem ((↑(w⁻¹) : LetA O n) ^ M) h
  rwa [← mul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul] at h'

theorem extDataOne_mem_Nl (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T)
    (hx : x ∈ W.N T) (hl : (letE i : LetA O n) • x = x) : x ∈ W.Nl T i :=
  hl ▸ liftb_letE_mem W T i hx

theorem extDataOne_exists [NeZero n] (W : LocWach PD LL O v n)
    (hH : Formalism.MainNotions.ElementDenominator.coreHerrExtΔ W) (hExt : liftb_HExt W) (hOne : liftb_HOne W)
    (hEx : ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
      IsSESLat (Qp := Qp) (O := O) ι π → Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧
        ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x)
    (hdex : W.DelF.card = PD.p - 1 → ∃ d : O, d * (W.DelF.card : O) = 1)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h6 : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hA : CaseA W) (hζ : ∃ ζ : LL, IsPrimitiveRoot ζ PD.p)
    (hOd : ∃ _ : IsDomain O, IsDiscreteValuationRing O ∧ IsFractionRing O LL)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (Mi hi : ZMod n → ℕ) (a N : ℕ)
    (hJY : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (Qp := Qp) (O := O) ι π → IsCrys PD Y.ρ → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W Y Mi hi)
    (hK : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (Qp := Qp) (O := O) ι π → IsCrys PD Y.ρ → ∀ i : ZMod n,
        Kills W π i (lp W N) ∧ Kills W π i (qp W ^ a))
    (c : G → T.V) (hc : c ∈ latticeFiniteCocycles PD T.L) :
    ∃ (y z : W.DD T) (μ ν : ZMod n → W.DD T) (h : (y, z) ∈ W.wachCocyclesDelta T) (hc' : c ∈ latticeCocycles T.L),
      W.clK T ⟨(y, z), h⟩ = Submodule.Quotient.mk (⟨c, hc'⟩ : ↥(latticeCocycles T.L)) ∧
        extDataOne_Rel W T Mi hi a N y z μ ν := by
  have hs : W.s = 1 := hA.2.1
  have hp2 : PD.p ≠ 2 := hA.2.2
  have hgK : W.gamK = W.gam := W.gamK_eq_one hs hp2
  have hcard : W.DelF.card = PD.p - 1 := by
    rw [(h9 T hT hs hp2).1, finrank_eq_one_case_A W hA, Nat.div_one]
  obtain ⟨d, hd⟩ := hdex hcard
  have hcZ : c ∈ latticeCocycles T.L := (Submodule.mem_inf.1 hc).1
  obtain ⟨Y, ι, π, hY, hext⟩ := hExt T c hT hc
  obtain ⟨hOc, -, e, he, hspan, hφe, hγe⟩ := hOne
  have hses := hext.1
  obtain ⟨hinj, hsurj, hker⟩ := hEx T Y W.one ι π hses
  have hsat : ∀ x, W.map ι x ∈ W.N Y → x ∈ W.N T := (h6.2.2 T Y W.one ι π hT hY hOc hses).2.2.2.1
  have hπι : ∀ x, W.map π (W.map ι x) = 0 := fun x => (hker _).2 ⟨x, rfl⟩
  obtain ⟨u, hu⟩ := hH hs hp2 T Y ι π hT hY c hcZ hext e ⟨hspan, hφe, hγe⟩
  obtain ⟨h9T, hmT⟩ := uniformizer_ring_and_module_clauses W h9 hA T hT
  obtain ⟨-, hmY⟩ := uniformizer_ring_and_module_clauses W h9 hA Y hY
  obtain ⟨-, hmO⟩ := uniformizer_ring_and_module_clauses W h9 hA W.one hOc
  have R := lifta_ring_of W h9T
  have hqΔ : qp W ∈ W.AΔ := lifta_qΔ W R.πΔ
  have hγdef : ∀ (T' : LocLat G Qp LL O) (x : W.DD T'), W.γ T' x = W.γD T' W.gam x := fun _ _ => rfl

  obtain ⟨e', he'd⟩ : ∃ e' : W.DD W.one, e' = ((u⁻¹ : Oˣ) : O) • e := ⟨_, rfl⟩
  have hφe' : W.φD W.one e' = e' := by rw [he'd, map_smul, hφe]
  have hγe' : ∀ g, W.γD W.one g e' = e' := fun g => by rw [he'd, map_smul, hγe]
  have hspan' : W.N W.one = Submodule.span (LetA O n) {e'} := by
    rw [hspan, he'd, ← algebraMap_smul (LetA O n) ((u⁻¹ : Oˣ) : O) e,
      Submodule.span_singleton_smul_eq ((u⁻¹).isUnit.map (algebraMap O (LetA O n)))]

  obtain ⟨X₀, hX₀⟩ := hsurj e'
  obtain ⟨X, hXd⟩ : ∃ X : W.DD Y, X = lifta_avg W Y d X₀ := ⟨_, rfl⟩
  have hXΔ : ∀ δ ∈ W.DelF, W.γD Y δ X = X := by rw [hXd]; exact lifta_avg_inv W Y d X₀
  have hXπ : W.map π X = e' := by
    rw [hXd, lifta_avg_map, hX₀]; exact lifta_avg_fix W W.one d hd e' (fun δ _ => hγe' δ)
  have hφX : W.map π (W.φD Y X - X) = 0 := by rw [map_sub, W.map_φ, hXπ, hφe', sub_self]
  have hγX : W.map π (W.γD Y W.gamK X - X) = 0 := by rw [map_sub, W.map_γ, hXπ, hγe', sub_self]
  obtain ⟨y, hy⟩ := (hker _).1 hφX
  obtain ⟨z, hz⟩ := (hker _).1 hγX
  have hz' : W.map ι z = W.γD Y W.gam X - X := by rw [hz, hgK]
  have hyΔ : ∀ δ ∈ W.DelF, W.γD T δ y = y := fun δ hδ => hinj (by
    rw [W.map_γ, hy, map_sub, ← W.φγ_comm, hXΔ δ hδ])
  have hzΔ : ∀ δ ∈ W.DelF, W.γD T δ z = z := fun δ hδ => hinj (by
    rw [W.map_γ, hz, map_sub, ← W.γD_mul, mul_comm, W.γD_mul, hXΔ δ hδ])
  have hcoc : (W.γD T W.gam y - y) - (W.φD T z - z) = 0 := hinj (by
    simp only [map_sub, W.map_γ, W.map_φ, hy, hz', W.φγ_comm, map_zero]
    abel)
  have hZ : (y, z) ∈ W.wachCocyclesDelta T := by
    rw [lifta_mem_Z1DΔ]
    refine ⟨?_, fun δ hδ => ⟨hyΔ δ hδ, hzΔ δ hδ⟩⟩
    rw [hgK]
    exact (liftb_mem_Z1D W T y z).2 hcoc
  have hcl : W.clK T ⟨(y, z), hZ⟩ = Submodule.Quotient.mk (⟨c, hcZ⟩ : ↥(latticeCocycles T.L)) := by
    rw [hu X ((u⁻¹ : Oˣ) : O) hXΔ (by rw [hXπ, he'd]) y z hZ hy hz, Units.mul_inv, one_smul]

  have he'N : e' ∈ W.N W.one := by
    rw [hspan']
    exact Submodule.mem_span_singleton_self e'
  have hKY := hK Y ι π hses hY
  have hlift : ∀ (i : ZMod n) (b : LetA O n), Kills W π i b → b ∈ W.AΔ →
      ∃ ε : W.DD Y, ε ∈ W.NΔ Y ∧ (letE i : LetA O n) • ε = ε ∧
        W.map π ε = b • (letE i : LetA O n) • e' := by
    intro i b hb hbΔ
    have hy0 : (letE i : LetA O n) • e' ∈ W.Nl W.one i :=
      extDataOne_mem_Nl W W.one i _ ((W.N W.one).smul_mem _ he'N) (idempotent_smul_smul W W.one i e')
    obtain ⟨ε₀, hε₀, hε₀π⟩ := Submodule.mem_map.1 (hb _ hy0)
    obtain ⟨m0, hm0, hm0e⟩ := Submodule.mem_map.1 hε₀
    have hε₀e : ε₀ = (letE i : LetA O n) • m0 := by
      rw [← hm0e, LinearMap.smul_apply (letE i : LetA O n) (LinearMap.id : W.DD Y →ₗ[LetA O n] W.DD Y) m0,
        LinearMap.id_apply]
    have h1 : W.map π ε₀ = b • (letE i : LetA O n) • e' := hε₀π
    refine ⟨lifta_avg W Y d ε₀, lifta_avg_N W Y d ε₀ (by rw [hε₀e]; exact (W.N Y).smul_mem _ hm0), ?_, ?_⟩
    · rw [← lifta_avg_smul W Y d _ (fun δ _ => gammaA_letter_idempotent W δ i), hε₀e, idempotent_smul_smul]
    · rw [lifta_avg_map, h1]
      refine lifta_avg_fix W W.one d hd _ (fun δ hδ => ?_)
      rw [gammaD_semilinear, hbΔ δ hδ, gammaD_idempotent_smul, hγe']
  have hlpΔ : lp W N ∈ W.AΔ := fun δ _ => gammaA_natCast_pow W δ N
  choose ε hεΔ hεl hεπ using fun i => hlift i (lp W N) (hKY i).1 hlpΔ
  choose x' hx'Δ hx'l hx'π using fun i => hlift i (qp W ^ a) (hKY i).2 (W.AΔ.pow_mem hqΔ a)
  have hεπ'' : ∀ j, W.map π (ε j) = ((PD.p : ℕ) : LetA O n) ^ N • (letE j : LetA O n) • e' := hεπ

  have hμex : ∀ i, ∃ m : W.DD T, W.map ι m = ε i - ((PD.p : ℕ) : LetA O n) ^ N • (letE i : LetA O n) • X :=
    fun i => (hker _).1 (by rw [map_sub, liftb_map_smul, liftb_map_smul, hXπ, hεπ'' i, sub_self])
  have hνex : ∀ i, ∃ m : W.DD T, W.map ι m = x' i - qp W ^ a • (letE i : LetA O n) • X := fun i =>
    (hker _).1 (by rw [map_sub, liftb_map_smul, liftb_map_smul, hXπ, hx'π i, sub_self])
  choose μ hμ using hμex
  choose ν hν using hνex
  refine ⟨y, z, μ, ν, hZ, hcZ, hcl, fun i => ?_⟩
  have hY5 := h5 Y Mi hi hY (hJY Y ι π hses hY)
  have hεNl : ∀ j, ε j ∈ W.Nl Y j := fun j => extDataOne_mem_Nl W Y j _ (hεΔ j).1 (hεl j)
  have hqaΔ : ∀ δ ∈ W.DelF, W.γA δ (qp W ^ a) = qp W ^ a := W.AΔ.pow_mem hqΔ a

  have hDLμ : DL W T i (μ i) := by
    refine ⟨hinj ?_, fun δ hδ => hinj ?_⟩
    · rw [liftb_map_smul, hμ i, smul_sub, hεl i,
        smul_comm (letE i : LetA O n) (((PD.p : ℕ) : LetA O n) ^ N), idempotent_smul_smul]
    · rw [W.map_γ, hμ i, map_sub, gammaD_semilinear, gammaA_natCast_pow, gammaD_idempotent_smul, hXΔ δ hδ,
        (hεΔ i).2 δ hδ]
  have hDLν : DL W T i (ν i) := by
    refine ⟨hinj ?_, fun δ hδ => hinj ?_⟩
    · rw [liftb_map_smul, hν i, smul_sub, hx'l i, smul_comm (letE i : LetA O n) (qp W ^ a),
        idempotent_smul_smul]
    · rw [W.map_γ, hν i, map_sub, gammaD_semilinear, hqaΔ δ hδ, gammaD_idempotent_smul, hXΔ δ hδ, (hx'Δ i).2 δ hδ]

  have h3 : InPN W T 1 (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • z) + (W.γ T (μ i) - μ i)) := by
    obtain ⟨w, hw, hwe⟩ := hmY.2 (ε i) (hεΔ i)
    have hπw : W.map π w = 0 := by
      apply extDataOne_π₀_cancel W R
      rw [← liftb_map_smul, ← hwe, map_sub, hγdef, W.map_γ, hεπ'' i, gammaD_semilinear, gammaA_natCast_pow,
        gammaD_idempotent_smul, hγe', sub_self]
    obtain ⟨t, ht⟩ := (hker _).1 hπw
    have htN : t ∈ W.N T := hsat t (by rw [ht]; exact hw.1)
    have htΔ : ∀ δ ∈ W.DelF, W.γD T δ t = t := fun δ hδ => hinj (by rw [W.map_γ, ht, hw.2 δ hδ])
    refine ⟨t, htN, htΔ, hinj ?_⟩
    rw [pow_one, liftb_map_smul W ι W.π₀ t, ht, ← hwe]
    simp only [natCast_pow_smul_eq_algebra W T N, map_add (f := _), map_sub, liftb_map_smul, hγdef, W.map_γ, hz', hμ i,
      gammaD_semilinear, gammaA_natCast_pow, gammaA_letter_idempotent, smul_sub]
    abel

  have hw4 : W.map ι (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y) + W.φD T (μ (i - 1)) - μ i) =
      W.φD Y (ε (i - 1)) - ε i := by
    simp only [natCast_pow_smul_eq_algebra W T N, map_add (f := _), map_sub, liftb_map_smul, W.map_φ, hy, hμ, liftb_φ_smul,
      frobeniusA_natCast_pow, wmap_φA_letE, smul_sub]
    abel
  have h4 : qp W ^ Mi i • (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y) + W.φD T (μ (i - 1)) - μ i) ∈
      W.N T := hsat _ (by
    rw [liftb_map_smul, hw4, smul_sub]
    exact sub_mem (extDataOne_Qqp W R hs _ _ _ (hY5.1 i _ (hεNl (i - 1))))
      ((W.N Y).smul_mem _ (hεΔ i).1))
  have h5' : ∃ s : ℕ, ((PD.p : ℕ) : O) ^ s • (qp W ^ hi i •
      (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y) + W.φD T (μ (i - 1)) - μ i)) ∈
        pullJ W T (i - 1) 1 := by
    refine ⟨N, ?_⟩
    have hxY : qp W ^ hi i • (W.φD Y (ε (i - 1)) - ε i) ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W Y (W.Nl Y (i - 1)) := by
      rw [smul_sub]
      exact sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨ε (i - 1), hεNl (i - 1), rfl⟩))
        (extDataOne_Qqp W R hs _ _ _ (hY5.2.1 i _ (hεNl i)))
    obtain ⟨p, hp, β, hβe, hβ0⟩ := pullback_span_of_exact W ι π hY hOc hker hsat hinj W.π₀ hmT e' hspan' i N
      (ε (i - 1)) (hεΔ (i - 1)).1 (hεπ'' (i - 1)) _ hxY
    have hβz : β • W.φD Y (ε (i - 1)) = 0 := by
      have hπ0 : W.map π (((PD.p : ℕ) : LetA O n) ^ N • (qp W ^ hi i • (W.φD Y (ε (i - 1)) - ε i))) = 0 := by
        rw [← hw4, ← liftb_map_smul, ← liftb_map_smul, hπι]
      rw [hβe, map_add (f := _), hπι, zero_add, liftb_map_smul, W.map_φ, hεπ'' (i - 1), liftb_φ_smul,
        frobeniusA_natCast_pow, frobenius_idempotent_shift, hφe', smul_smul, smul_smul] at hπ0
      by_cases he'0 : e' = 0
      · rw [hβ0 he'0, zero_smul]
      · have h1 := (basis_vector_eq_zero_or_torsionFree W e' hspan' W.π₀ hmO).resolve_left he'0 _ hπ0
        have h2 : β * (letE i : LetA O n) = 0 := eq_zero_of_natCast_pow_mul hζ hOd N _ (by rw [← h1]; ring)
        have h3 : W.φD Y (ε (i - 1)) = (letE i : LetA O n) • W.φD Y (ε (i - 1)) := by
          conv_lhs => rw [← hεl (i - 1)]
          exact frobenius_idempotent_shift W Y i _
        rw [h3, smul_smul, h2, zero_smul]
    have hfin : W.map ι (((PD.p : ℕ) : O) ^ N • (qp W ^ hi i •
        (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y) + W.φD T (μ (i - 1)) - μ i))) = W.map ι p := by
      rw [natCast_pow_smul_eq_algebra W T N (qp W ^ hi i • _), liftb_map_smul, liftb_map_smul, hw4, hβe, hβz, add_zero]
    rw [hinj hfin]
    exact hp
  have h6' : ((PD.p : ℕ) : O) ^ N • ν i - qp W ^ a • μ i ∈ W.N T := hsat _ (by
    rw [natCast_pow_smul_eq_algebra W T N, map_sub, liftb_map_smul, liftb_map_smul, hν i, hμ i, smul_sub, smul_sub,
      smul_comm (((PD.p : ℕ) : LetA O n) ^ N) (qp W ^ a) ((letE i : LetA O n) • X), sub_sub_sub_cancel_right]
    exact sub_mem ((W.N Y).smul_mem _ (hx'Δ i).1) ((W.N Y).smul_mem _ (hεΔ i).1))
  exact ⟨hDLμ, hDLν, h3, h4, h5', h6'⟩

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.NormOfVOne
section
noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation Topology Filter

variable {l : ℕ} [hl : Fact l.Prime]

theorem zetaQ_pow (P : LocPrime l) (j k : ℕ) : P.ζQ (j + k) ^ (l ^ k) = P.ζQ j := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, P.ζQ_succ, ih]

theorem chiQ_norm (P : LocPrime l) (h : GQ l) : ‖(P.χQ h : ℚ_[l])‖ = 1 := by
  have hroot : P.ζQ 1 ^ l = 1 := by
    have h0 := zetaQ_pow P 0 1
    rwa [zero_add, P.ζQ_zero, pow_one] at h0
  have hle : ∀ g : GQ l, ‖(P.χQ g : ℚ_[l])‖ ≤ 1 := by
    intro g
    obtain ⟨a, ha, -⟩ := P.χQ_cyc g 1 (P.ζQ 1) (by rwa [pow_one])
    have hA : ‖(a : ℚ_[l])‖ ≤ 1 := by
      have h2 : ‖((a : ℤ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((0 : ℕ) : ℤ)) := by
        first
          | exact (Padic.norm_int_le_pow_iff_dvd (a : ℤ) 0).2 (by simp)
          | exact (padicNormE.norm_int_le_pow_iff_dvd (a : ℤ) 0).2 (by simp)
      simpa using h2
    have hl1 : (l : ℝ) ^ (-((1 : ℕ) : ℤ)) ≤ 1 := by
      have h3 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_lt.le
      simp only [Nat.cast_one, zpow_neg, zpow_one]
      first
        | exact inv_le_one_of_one_le₀ h3
        | exact inv_le_one h3
    calc ‖(P.χQ g : ℚ_[l])‖ = ‖((P.χQ g : ℚ_[l]) - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ max ‖(P.χQ g : ℚ_[l]) - a‖ ‖(a : ℚ_[l])‖ := by
        first
          | exact Padic.nonarchimedean _ _
          | exact padicNormE.nonarchimedean _ _
          | exact IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (ha.trans hl1) hA
  have h1 := hle h
  have h2 := hle h⁻¹
  have hmul : ‖(P.χQ h : ℚ_[l])‖ * ‖(P.χQ h⁻¹ : ℚ_[l])‖ = 1 := by
    rw [← norm_mul, ← Units.val_mul, ← map_mul]
    simp
  exact le_antisymm h1 (by nlinarith [norm_nonneg (P.χQ h : ℚ_[l]), norm_nonneg (P.χQ h⁻¹ : ℚ_[l])])

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.StmtLocFOfCountsAll
section
noncomputable section

namespace Formalism.MainNotions.N.LocalShareBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Polynomial Filter Topology

theorem sum_pi_single {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α] (S0 : Finset α)
    (w : ι → α → ℝ) (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a ∈ S0, w i a ≤ 1) (v : ι) (P : α → Prop)
    [DecidablePred P] :
    ∑ t ∈ Fintype.piFinset (fun _ : ι => S0), (if P (t v) then ∏ i, w i (t i) else 0) ≤
      ∑ a ∈ S0.filter P, w v a := by
  set h : ι → α → ℝ := fun i a => if i = v then (if P a then w i a else 0) else w i a with hh
  have hpt : ∀ t : ι → α, (if P (t v) then ∏ i, w i (t i) else 0) = ∏ i, h i (t i) := by
    intro t
    by_cases hp : P (t v)
    · rw [if_pos hp]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i = v
      · subst hi; simp [hh, hp]
      · simp [hh, hi]
    · rw [if_neg hp]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hh, hp])
  rw [Finset.sum_congr rfl fun t _ => hpt t, ← Finset.prod_univ_sum, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
  have hv : ∑ a ∈ S0, h v a = ∑ a ∈ S0.filter P, w v a := by
    rw [Finset.sum_filter]; simp [hh]
  have hX : 0 ≤ ∑ a ∈ S0.filter P, w v a := Finset.sum_nonneg fun a _ => hw0 v a
  have hY : ∏ i ∈ Finset.univ.erase v, ∑ a ∈ S0, h i a ≤ 1 := by
    refine Finset.prod_le_one₀ (fun i _ => Finset.sum_nonneg fun a _ => ?_) fun i hi => ?_
    · simp only [hh]; split_ifs <;> first | exact hw0 _ _ | exact le_rfl
    · have hne : i ≠ v := Finset.ne_of_mem_erase hi
      simp only [hh, if_neg hne]
      exact hw1 i
  rw [hv]
  calc (∑ a ∈ S0.filter P, w v a) * ∏ i ∈ Finset.univ.erase v, ∑ a ∈ S0, h i a
      ≤ (∑ a ∈ S0.filter P, w v a) * 1 := mul_le_mul_of_nonneg_left hY hX
    _ = ∑ a ∈ S0.filter P, w v a := mul_one _

variable (D : D7)

variable {D}


end Formalism.MainNotions.N.LocalShareBounds
end
end

