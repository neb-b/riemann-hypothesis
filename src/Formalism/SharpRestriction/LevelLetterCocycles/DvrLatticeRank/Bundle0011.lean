module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0021
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfA
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.PhibOLComplete
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0029
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0009

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfB
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Mod

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem toLA_tmul (S : Submodule O (LcQ W T π' c)) (a : ↥W.AΔ) (s : ↥S) :
    toLA W T π' c S (a ⊗ₜ s) =
      algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T π' c) := rfl

theorem smulLA_tmul (a : LetA O n) (e : W.EE) (z : LcQ W T π' c) :
    smulLA W T π' c a (e ⊗ₜ z) = (algebraMap (LetA O n) W.EE a * e) ⊗ₜ z := rfl

theorem γLA_tmul (e : W.EE) (z : LcQ W T π' c) :
    γLA W T π' c (e ⊗ₜ z) = W.γE W.gamK e ⊗ₜ z := rfl

theorem smulLA_smulLA (a b : LetA O n) (x : LA W T π' c) :
    smulLA W T π' c a (smulLA W T π' c b x) = smulLA W T π' c (a * b) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul e z => rw [smulLA_tmul, smulLA_tmul, smulLA_tmul, ← mul_assoc, ← map_mul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem γLA_smulLA (a : LetA O n) (x : LA W T π' c) :
    γLA W T π' c (smulLA W T π' c a x) = smulLA W T π' c (W.γA W.gamK a) (γLA W T π' c x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul e z =>
    rw [smulLA_tmul, γLA_tmul, γLA_tmul, smulLA_tmul, map_mul, W.γE_ext]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem γA_comm (g h : W.Gam) (a : LetA O n) : W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
  funext i
  show W.γ₀ g (W.γ₀ h (a i)) = W.γ₀ h (W.γ₀ g (a i))
  rw [← AlgHom.mul_apply, ← map_mul, mul_comm g h, map_mul, AlgHom.mul_apply]

theorem γA_mem_AΔ (g : W.Gam) {a : LetA O n} (ha : a ∈ W.AΔ) : W.γA g a ∈ W.AΔ := by
  intro δ hδ
  rw [γA_comm, ha δ hδ]

theorem range_rep (u : LA W T π' c) (hu : u ∈ LinearMap.range (toLA W T π' c ⊤)) :
    ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T) (hy : ∀ j, y j ∈ NcS W T (c - 1)),
      u = ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ
        mkL W T π' c (y j) (hy j) := by
  classical
  obtain ⟨t, rfl⟩ := hu
  have ht : t ∈ Submodule.span O
      {t : ↥W.AΔ ⊗[O] ↥(⊤ : Submodule O (LcQ W T π' c)) | ∃ a s, a ⊗ₜ s = t} := by
    rw [TensorProduct.span_tmul_eq_top]
    trivial
  obtain ⟨m, f, g, hfg⟩ := Submodule.mem_span_set'.1 ht
  choose a s hs using fun j => (g j).2
  choose x hx using fun j =>
    Submodule.Quotient.mk_surjective _ ((s j : ↥(⊤ : Submodule O (LcQ W T π' c))) : LcQ W T π' c)
  refine ⟨m, fun j => f j • a j, fun j => (x j : W.DD T), fun j => (x j).2, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hfg, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hs j, TensorProduct.smul_tmul', toLA_tmul]
  congr 1
  exact (hx j).symm

theorem rep_mem {m : ℕ} (a : Fin m → LetA O n) (ha : ∀ j, a j ∈ W.AΔ) (y : Fin m → W.DD T)
    (hy : ∀ j, y j ∈ NcS W T (c - 1)) :
    ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ mkL W T π' c (y j) (hy j) ∈
      LinearMap.range (toLA W T π' c ⊤) :=
  Submodule.sum_mem _ fun j _ =>
    ⟨(⟨a j, ha j⟩ : ↥W.AΔ) ⊗ₜ (⟨mkL W T π' c (y j) (hy j), trivial⟩ : ↥(⊤ : Submodule O _)), rfl⟩

theorem smulLA_rep (b : LetA O n) {m : ℕ} (a : Fin m → LetA O n) (z : Fin m → LcQ W T π' c) :
    smulLA W T π' c b (∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ z j) =
      ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * (b * a j)) ⊗ₜ z j := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smulLA_tmul, ← map_mul]
  congr 2
  ring

theorem γLA_rep {m : ℕ} (a : Fin m → LetA O n) (z : Fin m → LcQ W T π' c) :
    γLA W T π' c (∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ z j) =
      ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * W.γA W.gamK (a j)) ⊗ₜ z j := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [γLA_tmul, W.γE_ext]
  congr 2
  show W.γA W.gamK ((letE c : LetA O n) * a j) = _
  rw [map_mul, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]

theorem range_smul {b : LetA O n} (hb : b ∈ W.AΔ) {u : LA W T π' c}
    (hu : u ∈ LinearMap.range (toLA W T π' c ⊤)) :
    smulLA W T π' c b u ∈ LinearMap.range (toLA W T π' c ⊤) := by
  obtain ⟨m, a, y, hy, rfl⟩ := range_rep W T π' c u hu
  rw [smulLA_rep]
  exact rep_mem W T π' c _ (fun j => W.AΔ.mul_mem hb (a j).2) y hy

theorem range_γ {u : LA W T π' c} (hu : u ∈ LinearMap.range (toLA W T π' c ⊤)) :
    γLA W T π' c u ∈ LinearMap.range (toLA W T π' c ⊤) := by
  obtain ⟨m, a, y, hy, rfl⟩ := range_rep W T π' c u hu
  rw [γLA_rep]
  exact rep_mem W T π' c _ (fun j => γA_mem_AΔ W _ (a j).2) y hy

theorem mem_LamLA (x : LA W T π' c) :
    x ∈ LamLA W T π' Eπ h' c ⊤ ↔
      smulLA W T π' c (Eπ ^ h') x ∈ LinearMap.range (toLA W T π' c ⊤) := Iff.rfl

theorem LamLA_smul {a : LetA O n} (ha : a ∈ W.AΔ) {x : LA W T π' c}
    (hx : x ∈ LamLA W T π' Eπ h' c ⊤) : smulLA W T π' c a x ∈ LamLA W T π' Eπ h' c ⊤ := by
  rw [mem_LamLA, smulLA_smulLA, mul_comm, ← smulLA_smulLA]
  exact range_smul W T π' c ha hx

theorem LamLA_γ {u u' : LetA O n} (hu' : u' ∈ W.AΔ) (huu : u' * u = 1)
    (hγE : W.γA W.gamK Eπ = u * Eπ) {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤) :
    γLA W T π' c x ∈ LamLA W T π' Eπ h' c ⊤ := by
  rw [mem_LamLA]
  have h1 : Eπ ^ h' = u' ^ h' * W.γA W.gamK (Eπ ^ h') := by
    rw [map_pow, hγE, mul_pow, ← mul_assoc, ← mul_pow, huu, one_pow, one_mul]
  rw [h1, ← smulLA_smulLA, ← γLA_smulLA]
  exact range_smul W T π' c (W.AΔ.pow_mem hu' h') (range_γ W T π' c hx)

theorem NL_le_LamLA (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) :
    NL W T Pt π' Eπ h' c ≤ LamLA W T π' Eπ h' c ⊤ := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨m, a, y, ⟨hy, heq⟩, -⟩
  rw [SetLike.mem_coe, mem_LamLA, heq]
  exact rep_mem W T π' c _ (fun j => (a j).2) y hy

theorem φspan_γ (g : W.Gam) {z : W.DD T} (hz : z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))) :
    W.γD T g z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.1 hx
    rw [← W.φγ_comm]
    apply Submodule.subset_span
    refine ⟨W.γD T g (((letE (c - 1) : LetA O n) • LinearMap.id) x₀), ?_, rfl⟩
    show W.γD T g ((letE (c - 1) : LetA O n) • x₀) ∈ W.Nl T (c - 1)
    rw [γD_letE]
    exact ⟨W.γD T g x₀, W.N_Γ T g x₀ hx₀, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul]; exact Submodule.smul_mem _ _ hx

theorem DelS_γ (g : W.Gam) {x : W.DD T} (hx : x ∈ DelS W T) : W.γD T g x ∈ DelS W T := by
  rw [mem_DelS] at hx ⊢
  intro δ hδ
  rw [← W.γD_mul, mul_comm, W.γD_mul, hx δ hδ]

theorem LamPS_γ {u u' : LetA O n} (huu : u' * u = 1) (hγE : W.γA W.gamK Eπ = u * Eπ) {y : W.DD T}
    (hy : y ∈ LamPS W T Eπ h' c) : W.γD T W.gamK y ∈ LamPS W T Eπ h' c := by
  rw [mem_LamPS] at hy ⊢
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · have e : Eπ ^ h' = u' ^ h' * W.γA W.gamK (Eπ ^ h') := by
      rw [map_pow, hγE, mul_pow, ← mul_assoc, ← mul_pow, huu, one_pow, one_mul]
    rw [e, mul_smul, ← Formalism.MainNotions.LiftingTheory.wmap_γD_smul]
    exact Submodule.smul_mem _ _ (φspan_γ W T c _ h1)
  · exact (mem_DelS W T _).1 (DelS_γ W T _ ((mem_DelS W T y).2 h2))
  · rw [← γD_letE, h3]

theorem LamPS_smul {a : LetA O n} (ha : a ∈ W.AΔ) {y : W.DD T} (hy : y ∈ LamPS W T Eπ h' c) :
    a • y ∈ LamPS W T Eπ h' c := by
  rw [mem_LamPS] at hy ⊢
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · rw [smul_comm]
    exact Submodule.smul_mem _ _ h1
  · intro δ hδ
    rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, ha δ hδ, h2 δ hδ]
  · rw [smul_comm, h3]

theorem Eπ_φspan {w : LetA O n} {w' : LetA O n} (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    (h5 : ∀ x ∈ W.Nl T (c - 1), W.Q ^ h' • W.φD T x ∈ W.N T) {z : W.DD T}
    (hz : z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))) : Eπ ^ h' • z ∈ W.N T := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    have e : Eπ ^ h' = w' ^ h' * W.Q ^ h' := by
      rw [hQ, mul_pow, ← mul_assoc, ← mul_pow, hww, one_pow, one_mul]
    rw [e, mul_smul]
    exact Submodule.smul_mem _ _ (h5 x hx)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem JP_mem {w w' : LetA O n} (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    (h5 : ∀ x ∈ W.Nl T (c - 1), W.Q ^ h' • W.φD T x ∈ W.N T) (M j : ℕ) (hj : j ≤ M) {y : W.DD T}
    (hy : y ∈ JP W T π' Eπ h' M c) : ∃ z ∈ W.N T, y = π' ^ j • z := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hy
  have hpφ : p ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1)) := hp.1.1
  refine ⟨(π' ^ (M - j) * Eπ ^ (2 * h')) • (Eπ ^ h' • p),
    Submodule.smul_mem _ _ (Eπ_φspan W T Eπ h' c hww hQ h5 hpφ), ?_⟩
  show (π' ^ M * Eπ ^ (3 * h')) • p = _
  rw [smul_smul, smul_smul]
  congr 1
  rw [show 3 * h' = 2 * h' + h' by ring, pow_add Eπ]
  conv_lhs => rw [show M = j + (M - j) by omega, pow_add]
  ring

theorem tf_smul {a : LetA O n} (ha : IsUnit (algebraMap (LetA O n) W.EE a)) {x : W.DD T}
    (hx : a • x = 0) : x = 0 := by
  obtain ⟨u, hu⟩ := ha
  have h1 : (u : W.EE) • x = 0 := by rw [hu, algebraMap_smul]; exact hx
  have h2 := congrArg (fun y => ((u⁻¹ : W.EEˣ) : W.EE) • y) h1
  simpa [smul_smul] using h2

end Mod

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfB
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MQ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

section Div

variable {O : Type} [CommRing O]

theorem phibN_div (p : ℕ) (hp : p.Prime) [Nontrivial O] [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O] (N : ℕ)
    (f : PowerSeries O) : ∃ (Q : PowerSeries O) (R : Polynomial O), R.degree < ((p * N : ℕ) : WithBot ℕ) ∧
      f = ((1 + PowerSeries.X) ^ p - 1) ^ N * Q + (R : PowerSeries O) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set I : Ideal O := Ideal.span {((p : ℕ) : O)} with hI
  have hjac : I ≤ (⊥ : Ideal O).jacobson := by
    first
    | exact IsAdicComplete.le_jacobson_bot I
    | exact IsAdicComplete.le_jacobson_bot (I := I)
  have hIne : I ≠ ⊤ := by
    intro h
    rw [h, top_le_iff, Ideal.jacobson_eq_top_iff] at hjac
    exact bot_ne_top hjac
  have hp2 : ((p : ℕ) : O) ∈ nonunits O :=
    mem_nonunits_iff.2 (fun hu => hIne (Ideal.span_singleton_eq_top.2 hu))
  haveI hch : CharP (O ⧸ I) p := CharP.quotient O p hp2
  haveI : Nontrivial (O ⧸ I) := by
    first
    | exact Ideal.Quotient.nontrivial_iff.2 hIne
    | exact Submodule.Quotient.nontrivial_of_lt_top _ hIne.lt_top
    | exact Ideal.Quotient.nontrivial_of_lt_top hIne.lt_top
  have hinj : Function.Injective (algebraMap (O ⧸ I) (PowerSeries (O ⧸ I))) := by
    intro a b hab
    first
    | simpa using congrArg (PowerSeries.constantCoeff (O ⧸ I)) hab
    | simpa using congrArg PowerSeries.constantCoeff hab
    | simpa using congrArg (PowerSeries.coeff 0) hab
    | exact PowerSeries.C_injective hab
  haveI : CharP (PowerSeries (O ⧸ I)) p := charP_of_injective_algebraMap hinj p
  have hmap : PowerSeries.map (Ideal.Quotient.mk I) (((1 + PowerSeries.X) ^ p - 1) ^ N) =
      PowerSeries.X ^ (p * N) := by
    simp only [map_pow, map_sub, map_add (f := _), map_one, PowerSeries.map_X]
    rw [add_pow_char, one_pow, add_sub_cancel_left, ← pow_mul]
  have key : ∀ c : O, Ideal.Quotient.mk I c = 1 → IsUnit c := by
    intro c hc
    have hmem : c - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hc, map_one, sub_self]
    have hj := (Ideal.mem_jacobson_bot.1 (hjac hmem)) 1
    simpa using hj
  have hdiv : (((1 + PowerSeries.X) ^ p - 1) ^ N : PowerSeries O).IsWeierstrassDivisorAt I := by
    show IsUnit _
    rw [hmap, PowerSeries.order_X_pow, ENat.toNat_coe]
    apply key
    rw [← PowerSeries.coeff_map, hmap, PowerSeries.coeff_X_pow_self]
  have hW := hdiv.isWeierstrassDivisionAt_div_mod f
  refine ⟨hdiv.div f, hdiv.mod f, ?_, ?_⟩
  · have hd := hW.degree_lt
    rw [hmap, PowerSeries.order_X_pow, ENat.toNat_coe] at hd
    exact_mod_cast hd
  · exact hW.eq_mul_add

end Div

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem delF_mul' {g h : W.Gam} (hg : g ∈ W.DelF) (hh : h ∈ W.DelF) : g * h ∈ W.DelF := by
  rw [W.DelF_def] at hg hh ⊢
  obtain ⟨k₁, hk₁, h₁⟩ := hg
  obtain ⟨k₂, hk₂, h₂⟩ := hh
  exact ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, by
    rw [mul_pow, pow_mul, h₁, one_pow, one_mul, mul_comm k₁ k₂, pow_mul, h₂, one_pow]⟩

theorem delF_inv' {g : W.Gam} (hg : g ∈ W.DelF) : g⁻¹ ∈ W.DelF := by
  rw [W.DelF_def] at hg ⊢
  obtain ⟨k, hk, h⟩ := hg
  exact ⟨k, hk, by rw [inv_pow, h, inv_one]⟩

theorem γA_mul' (g h : W.Gam) (a : LetA O n) : W.γA (g * h) a = W.γA g (W.γA h a) := by
  funext i
  show W.γ₀ (g * h) (a i) = W.γ₀ g (W.γ₀ h (a i))
  rw [map_mul, AlgHom.mul_apply]

theorem letE_mem (c : ZMod n) : (letE c : LetA O n) ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ (letE c : LetA O n) = letE c
  intro δ _
  funext i
  show W.γ₀ δ ((letE c : LetA O n) i) = (letE c : LetA O n) i
  simp only [letE, Pi.single_apply]
  split_ifs <;> simp

theorem letE_mul_self' (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  simp only [letE, Pi.mul_apply, Pi.single_apply]
  split_ifs <;> simp

def avg (u : Oˣ) (x : LetA O n) : LetA O n := ((u⁻¹ : Oˣ) : O) • ∑ δ ∈ W.DelF, W.γA δ x

theorem avg_mem (u : Oˣ) (x : LetA O n) : avg W u x ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ (avg W u x) = avg W u x
  intro δ' hδ'
  unfold avg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_nbij' (fun δ => δ' * δ) (fun δ => δ'⁻¹ * δ) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    exact delF_mul' W hδ' ha
  · intro a ha
    exact delF_mul' W (delF_inv' W hδ') ha
  · intro a _
    exact inv_mul_cancel_left δ' a
  · intro a _
    exact mul_inv_cancel_left δ' a
  · intro a _
    exact (γA_mul' W δ' a x).symm

theorem avg_self (u : Oˣ) (hu : (u : O) = (W.DelF.card : ℕ)) {x : LetA O n} (hx : x ∈ W.AΔ) :
    avg W u x = x := by
  have hx' : ∀ δ ∈ W.DelF, W.γA δ x = x := hx
  unfold avg
  rw [Finset.sum_congr rfl (fun δ hδ => hx' δ hδ), Finset.sum_const, ← Nat.cast_smul_eq_nsmul O, ← hu,
    smul_smul, Units.inv_mul, one_smul]

theorem avg_add (u : Oˣ) (x y : LetA O n) : avg W u (x + y) = avg W u x + avg W u y := by
  simp only [avg, map_add (f := _), Finset.sum_add_distrib, smul_add]

theorem avg_mul_left (u : Oˣ) {y : LetA O n} (hy : y ∈ W.AΔ) (x : LetA O n) :
    avg W u (y * x) = y * avg W u x := by
  have hy' : ∀ δ ∈ W.DelF, W.γA δ y = y := hy
  have hs : ∑ δ ∈ W.DelF, W.γA δ (y * x) = y * ∑ δ ∈ W.DelF, W.γA δ x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun δ hδ => by rw [map_mul, hy' δ hδ])
  unfold avg
  rw [hs, mul_smul_comm]

theorem avg_sum (u : Oˣ) {ι : Type} (s : Finset ι) (f : ι → LetA O n) :
    avg W u (∑ i ∈ s, f i) = ∑ i ∈ s, avg W u (f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [avg, map_sum, Finset.smul_sum]
  exact Finset.sum_comm

theorem div_at (hp : PD.p.Prime) [Nontrivial O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (s' h' : ℕ) (π' Eπ : LetA O n) (w₁ w₂ : (LetA O n)ˣ) (hπ : π' = w₁ * (letπ : LetA O n) ^ s') (hq : W.q = w₂ * Eπ)
    (u : Oˣ) (hu : (u : O) = (W.DelF.card : ℕ)) (hπΔ : π' ∈ W.AΔ) (hEΔ : Eπ ∈ W.AΔ) (c : ZMod n) :
    ∃ (D : ℕ) (S : Fin D → ↥W.AΔ), ∀ a : ↥W.AΔ, ∃ (co : Fin D → O) (s : ↥W.AΔ),
      (letE c : LetA O n) * a = (letE c : LetA O n) * (∑ r, algebraMap O (LetA O n) (co r) * (S r : LetA O n)) +
        (letE c : LetA O n) * (π' * Eπ ^ (2 * h') * s) := by
  classical
  set N := s' + 2 * h' with hN
  refine ⟨PD.p * N, fun i => ⟨avg W u ((letπ : LetA O n) ^ (i : ℕ)), avg_mem W u _⟩, fun a => ?_⟩
  obtain ⟨Q, R, hR, hf⟩ := phibN_div (O := O) PD.p hp N ((a : LetA O n) c)
  set A1 : PowerSeries O := (w₁ : LetA O n) c
  set B1 : PowerSeries O := ((w₁⁻¹ : (LetA O n)ˣ) : LetA O n) c
  set A2 : PowerSeries O := (w₂ : LetA O n) c
  set B2 : PowerSeries O := ((w₂⁻¹ : (LetA O n)ˣ) : LetA O n) c
  have h1 : A1 * B1 = 1 := by
    have := congrFun (Units.mul_inv w₁) c
    simpa using this
  have h2 : A2 * B2 = 1 := by
    have := congrFun (Units.mul_inv w₂) c
    simpa using this
  have hq0 : W.q₀ = A2 * Eπ c := by
    have := congrFun hq c
    simpa [LocWach.q] using this
  have hEc : Eπ c = B2 * W.q₀ := by
    rw [hq0, ← mul_assoc, mul_comm B2 A2, h2, one_mul]
  have hπc : π' c = A1 * PowerSeries.X ^ s' := by
    have := congrFun hπ c
    simpa [letπ] using this
  have hφb : (1 + PowerSeries.X) ^ PD.p - 1 = PowerSeries.X * W.q₀ := by
    rw [W.q₀_def, add_comm]
  have key : A1 * B1 * (A2 * B2) ^ (2 * h') = 1 := by rw [h1, h2, one_pow, one_mul]
  set s₀ : LetA O n := fun _ => PowerSeries.X ^ (2 * h') * W.q₀ ^ s' * B1 * A2 ^ (2 * h') * Q with hs₀
  set Rt : LetA O n := fun _ => (R : PowerSeries O) with hRt
  have hcl : (letE c : LetA O n) * a = (letE c : LetA O n) * Rt + (letE c : LetA O n) * (π' * Eπ ^ (2 * h') * s₀) := by
    funext i
    by_cases hi : i = c
    · subst hi
      simp only [Pi.add_apply, Pi.mul_apply, letE, Pi.single_eq_same, one_mul, Pi.pow_apply, hs₀, hRt]
      rw [hf, hφb, hπc, hEc]
      linear_combination (-(PowerSeries.X ^ (s' + 2 * h') * W.q₀ ^ (s' + 2 * h') * Q)) * key
    · simp [letE, Pi.single_apply, hi]
  have hR' : Rt = ∑ i : Fin (PD.p * N), algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ) := by
    have hdeg : ∀ m, PD.p * N ≤ m → R.coeff m = 0 := fun m hm =>
      Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hR (by exact_mod_cast hm))
    funext j
    show (R : PowerSeries O) = (∑ i : Fin (PD.p * N), algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ)) j
    rw [Finset.sum_apply]
    ext k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Polynomial.coeff_coe, map_sum]
    have ht : ∀ i : Fin (PD.p * N), PowerSeries.coeff k ((algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ)) j) =
        if k = (i : ℕ) then R.coeff k else 0 := by
      intro i
      have e : (algebraMap O (LetA O n) (R.coeff i) * (letπ : LetA O n) ^ (i : ℕ)) j = R.coeff i • PowerSeries.X ^ (i : ℕ) := by
        rw [← Algebra.smul_def]
        rfl
      rw [e, map_smul, PowerSeries.coeff_X_pow, smul_eq_mul]
      split_ifs with h
      · rw [h, mul_one]
      · rw [mul_zero]
    rw [Finset.sum_congr rfl (fun i _ => ht i),
      Fin.sum_univ_eq_sum_range (fun i => if k = i then R.coeff k else 0) (PD.p * N), Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · rw [Finset.mem_range, not_lt] at hk
      exact hdeg k hk
  have hg : π' * Eπ ^ (2 * h') ∈ W.AΔ := mul_mem hπΔ (pow_mem hEΔ _)
  have hae : (letE c : LetA O n) * a ∈ W.AΔ := mul_mem (letE_mem W c) a.2
  refine ⟨fun i => R.coeff i, ⟨avg W u s₀, avg_mem W u _⟩, ?_⟩
  calc (letE c : LetA O n) * a = avg W u ((letE c : LetA O n) * a) := (avg_self W u hu hae).symm
    _ = avg W u ((letE c : LetA O n) * Rt + (letE c : LetA O n) * (π' * Eπ ^ (2 * h') * s₀)) := by rw [hcl]
    _ = (letE c : LetA O n) * avg W u Rt + (letE c : LetA O n) * (π' * Eπ ^ (2 * h') * avg W u s₀) := by
      rw [avg_add, avg_mul_left W u (letE_mem W c), avg_mul_left W u (letE_mem W c), avg_mul_left W u hg]
    _ = _ := by
      rw [hR', avg_sum]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [avg_mul_left W u (Subalgebra.algebraMap_mem _ _)]

end Formalism.MainNotions.N.Ln34.MQ
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3uplinkPfOf
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

theorem u3uplink_pf_of (hW : WStep) : UpSlotOfModels := by
  intro D HW F Cm CA CB CK hA hMF
  exact u3upPf_ofR D HW hMF (hW D HW F Cm CA CB CK hA) (ninlam_pf D HW F Cm CA CB CK hA)
    (gamPiCondition D HW F Cm CA CB CK hA)

end Formalism.MainNotions.N.Ln34

end
end

