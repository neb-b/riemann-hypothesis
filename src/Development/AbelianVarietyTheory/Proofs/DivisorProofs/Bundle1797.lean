module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartCharacterIsLogarithm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1785
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicL2LimitZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_l2_limit_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _))
    (D : (κ → AdeleRing (𝓞 F) F) → ℂ) (G : ℕ → (κ → AdeleRing (𝓞 F) F) → ℂ), (∀ n, G n ∈ GlobalTheory.WeilM.schA F κ) →
    (∀ a, Filter.Tendsto (fun n => G n a) Filter.atTop (nhds (D a))) →
    Filter.Tendsto (fun n => GlobalTheory.WeilL2Words.l2A F μ (G n)) Filter.atTop (nhds 0) → GlobalTheory.WeilL2Words.l2A F μ D = 0 := by
  first | exact @GlobalTheory.WeilL2Words.l2A_eq_zero_of_tendsto | exact GlobalTheory.WeilL2Words.l2A_eq_zero_of_tendsto | (intros; apply GlobalTheory.WeilL2Words.l2A_eq_zero_of_tendsto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSub
section
set_option autoImplicit false

noncomputable section

open MvPolynomial
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD GlobalTheory.ExpFrame

namespace GlobalTheory.HighWtEmb

abbrev BVar (N : ℕ) (ι : Type) : Type := ι × (Fin N × Fin N)

abbrev OVar (N : ℕ) {ι : Type} (τ : ι) : Type := {p : BVar N ι // p.1 ≠ τ}

def blockRed (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι) :
    MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (BVar N ι) (O ⧸ Ideal.span {ϖ}) :=
  aeval fun v => X (τ, v)

def redT (O : Type) [CommRing O] (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) :
    NablaT O N mu →ₗ[O] MvPolynomial (BVar N ι) (O ⧸ Ideal.span {ϖ}) :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra O ι (MvPolynomial (BVar N ι) (O ⧸ Ideal.span {ϖ}))).compLinearMap
    fun τ => (blockRed O N ϖ τ).toLinearMap ∘ₗ (dualWeyl O N N (res N (mu τ))).subtype)

def nabK (k : Type) [CommRing k] (N : ℕ) {ι : Type} [Fintype ι] (ν : ι → Fin N → ℕ) : Submodule k (MvPolynomial (BVar N ι) k) :=
  Submodule.span k {P | ∃ f : ι → MvPolynomial (Fin N × Fin N) k, (∀ τ, f τ ∈ dualWeyl k N N (ν τ)) ∧
    P = ∏ τ, rename (fun v : Fin N × Fin N => ((τ, v) : BVar N ι)) (f τ)}

def toBlock (k : Type) [CommRing k] (N : ℕ) {ι : Type} [DecidableEq ι] (τ : ι) :
    MvPolynomial (BVar N ι) k →ₐ[k] MvPolynomial (Fin N × Fin N) (MvPolynomial (OVar N τ) k) :=
  aeval fun p => if h : p.1 = τ then X p.2 else C (X ⟨p, h⟩)

def blockSub (k : Type) [CommRing k] (N : ℕ) {ι : Type} (A : ι → Matrix (Fin N) (Fin N) k) :
    MvPolynomial (BVar N ι) k →ₐ[k] MvPolynomial (BVar N ι) k :=
  aeval fun p => ∑ b : Fin N, C (A p.1 p.2.1 b) * X (p.1, (b, p.2.2))

def blockW (N : ℕ) {ι : Type} [DecidableEq ι] (τ : ι) : BVar N ι → (Fin N → ℕ) :=
  fun p => if p.1 = τ then Pi.single p.2.1 1 else 0

end GlobalTheory.HighWtEmb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtSmallPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelCharExp

open Formalism.BasicNotions.TH Formalism.IndefR.Lev

theorem pow_of_dvd {G : Type} [Monoid G] {x : G} {n M : ℕ} (h : x ^ n = 1) (hd : n ∣ M) : x ^ M = 1 := by
  obtain ⟨k, rfl⟩ := hd
  rw [pow_mul, h, one_pow]

theorem prod_pow_eq_one {ι G : Type} [CommMonoid G] (s : Finset ι) (f : ι → G) (M : ℕ) (h : ∀ i ∈ s, f i ^ M = 1) :
    (∏ i ∈ s, f i) ^ M = 1 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one h

theorem residue_char_pow {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) {LL : Type} [Monoid LL]
    (χ : (Formalism.L2.DIV.kP PP)ˣ →* LL) (u : (Formalism.L2.DIV.kP PP)ˣ) : χ u ^ Nat.card (Formalism.L2.DIV.kP PP)ˣ = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

theorem card_units_pos {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) : 0 < Nat.card (Formalism.L2.DIV.kP PP)ˣ := by
  have : Finite (Formalism.L2.DIV.kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  exact Nat.card_pos


open Classical in
def expOf {D : D7} {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : ℕ :=
  ∏ PP ∈ L.Pg ∪ L.Q, Nat.card (Formalism.L2.DIV.kP PP)ˣ

theorem expOf_pos {D : D7} {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : 0 < expOf L :=
  Finset.prod_pos fun PP _ => card_units_pos PP

open Classical in
theorem levFn_flag1_pow {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (x : GL (Fin V.rank) (Lev.EAf D)) :
    Formalism.L2.DIV.levFn β (flag1L L) x ^ expOf L = 1 := by
  have h1 : Formalism.L2.DIV.ext1 (flag1L L).P.H (flag1L L).P.chi (Formalism.L2.DIV.rTup β (flag1L L) x) = 1 :=
    Formalism.IndefR.Lev.subgroupCharExtension_one_apply _ _
  unfold Formalism.L2.DIV.levFn
  rw [h1, one_mul, mul_pow]
  have hd : ∀ PP ∈ L.Pg ∪ L.Q, Nat.card (Formalism.L2.DIV.kP PP)ˣ ∣ expOf L := fun PP hP =>
    Finset.dvd_prod_of_mem (fun PP => Nat.card (Formalism.L2.DIV.kP PP)ˣ) hP
  rw [prod_pow_eq_one _ _ _ ?_, prod_pow_eq_one _ _ _ ?_, one_mul]
  · intro PP hP
    exact pow_of_dvd (residue_char_pow PP _ _) (hd PP (Finset.mem_union_right _ hP))
  · intro PP hP
    refine prod_pow_eq_one _ _ _ fun c _ => ?_
    exact pow_of_dvd (residue_char_pow PP _ _) (hd PP (Finset.mem_union_left _ hP))

theorem levEnv_chi_pow : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J), (levEnv V β L).χ k ^ expOf L = 1 := by
  intro D V β L k
  exact levFn_flag1_pow V β L _

end GlobalTheory.LevelCharExp

end

namespace GlobalTheory.LevelCharExp

end GlobalTheory.LevelCharExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace GlobalTheory.CharInvForm

theorem exists_schwartz_one (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ f₀ : SchwartzMap V ℂ, f₀ 0 = 1 := by
  obtain ⟨f, -, hc, hs, -, h1⟩ :=
    exists_contDiff_tsupport_subset (x := (0 : V)) (s := Set.univ) (n := ⊤) Filter.univ_mem
  have hc' : HasCompactSupport (fun x => (f x : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hs' : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hs
  exact ⟨hc'.toSchwartzMap hs', by simp [h1]⟩

theorem arch (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →L[ℂ] ℂ)
    (hT : ∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap V ℂ, T f = a * f 0 := by
  obtain ⟨f₀, hf₀⟩ := exists_schwartz_one V
  refine ⟨T f₀, fun f => ?_⟩
  have h0 : (f - f 0 • f₀) 0 = 0 := by simp [hf₀]
  obtain ⟨n, L, h, g, hg, hsum⟩ := GlobalTheory.SchwartzDiv.hadamard V _ h0
  have e : f - f 0 • f₀ = ∑ i, g i := by
    ext x
    rw [hsum x, SchwartzMap.sum_apply]
  have : T (f - f 0 • f₀) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    exact Finset.sum_eq_zero fun i _ => GlobalTheory.CharFormDeriv.charForm_kills_linear_mul V T hT (L i) (h i) (g i) (hg i)
  rw [map_sub, map_smul, sub_eq_zero] at this
  rw [this, smul_eq_mul, mul_comm]

end GlobalTheory.CharInvForm

namespace GlobalTheory.CharInvForm

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem pairA_zero_add (a b : Af F) : pairA F 0 (a + b) = pairA F 0 a + pairA F 0 b :=
  Prod.ext (zero_add (0 : Ainf F)).symm rfl

theorem dot_pairA_fin {κ : Type} [Fintype κ] (x : κ → AF F) (y : κ → Af F) :
    (x ⬝ᵥ fun i => pairA F 0 (y i)) = pairA F 0 ((fun i => (x i).2) ⬝ᵥ y) := by
  have h1 : (RingHom.fst (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F 0 (y i)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul]
    exact Finset.sum_eq_zero fun i _ => by
      show (RingHom.fst (Ainf F) (Af F)) (x i) * 0 = 0
      exact mul_zero _
  have h2 : (RingHom.snd (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F 0 (y i)) = (fun i => (x i).2) ⬝ᵥ y := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul]
    rfl
  exact Prod.ext h1 h2

theorem dot_pairA_inf {κ : Type} [Fintype κ] (x : κ → AF F) (y : κ → Ainf F) :
    (x ⬝ᵥ fun i => pairA F (y i) 0) = pairA F (∑ i, (x i).1 * y i) 0 := by
  have h1 : (RingHom.fst (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F (y i) 0) = ∑ i, (x i).1 * y i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul]
    rfl
  have h2 : (RingHom.snd (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F (y i) 0) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul]
    exact Finset.sum_eq_zero fun i _ => by
      show (RingHom.snd (Ainf F) (Af F)) (x i) * 0 = 0
      exact mul_zero _
  exact Prod.ext h1 h2

theorem mem_schA {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem pureA_zero {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) :
    pureA F f g 0 = f 0 * g 0 := by
  simp only [pureA]
  congr 2
  · funext i
    exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

end GlobalTheory.CharInvForm

namespace GlobalTheory.CharInvForm

open scoped Classical

theorem psi_dot_inf {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (x : κ → AF F) (Y : κ → mixedEmbedding.mixedSpace F) :
    ψ (x ⬝ᵥ fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0) =
      Complex.exp (Complex.I * ((-(2 * Real.pi) * ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) i * Y i) : ℝ) : ℂ)) := by
  have hat : At (evI F) (pairA F (∑ i, (x i).1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0) := by
    intro u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    show (u.1 * _, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
    rw [h1, zero_mul, mul_zero]
  rw [dot_pairA_inf, hψ.2.2 _ hat]
  show Complex.exp (_ * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
    (InfiniteAdeleRing.ringEquiv_mixedSpace F (∑ i, (x i).1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i))) : ℝ) : ℂ)) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  simp only [map_mul, RingEquiv.apply_symm_apply]
  congr 1
  push_cast
  ring

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm κ →
    (∀ (y : κ → AF F), ∀ φ ∈ schA F κ, l (fun x => ψ (x ⬝ᵥ y) * φ x) = l φ) →
    ∃ c : ℂ, ∀ φ ∈ schA F κ, l φ = c * φ 0 := by
  intro F _ _ ψ hψ κ _ l hl hinv

  have harch : ∀ g ∈ SB (κ → Af F), ∃ α : ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f g) = α * f 0 := by
    intro g hg
    obtain ⟨T, hT⟩ := hl g hg
    obtain ⟨α, hα⟩ := arch _ T (by
      intro L f f' hff'
      obtain ⟨Y, hY⟩ := GlobalTheory.TraceDual.exists_trace_rep F κ L
      rw [← hT, ← hT, ← hinv (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0)
        (pureA F f g) (mem_schA f hg)]
      congr 1
      funext x
      simp only [pureA, hff', psi_dot_inf hψ, hY, mul_assoc])
    exact ⟨α, fun f => (hT f).trans (hα f)⟩

  obtain ⟨f₀, hf₀⟩ := exists_schwartz_one (κ → mixedEmbedding.mixedSpace F)
  let a : ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => l (pureA F f₀ g)
      map_add' := fun g g' => by
        rw [← map_add (f := _)]
        congr 1
        funext x
        simp [pureA, mul_add]
      map_smul' := fun s g => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        funext x
        simp [pureA, mul_comm, mul_assoc] }
  obtain ⟨c, hc⟩ := GlobalTheory.CharForm.exists_eq_mul_apply_zero (κ → Af F) {χ | ∃ y : κ → Af F, χ = fun x => ψ (pairA F 0 (x ⬝ᵥ y))}
    (by
      intro N hN
      obtain ⟨U, hUo, hUc, hUN, hsep⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ N hN
      refine ⟨U, hUo, hUc, hUN, fun x₀ hx₀ => ?_⟩
      obtain ⟨y, hyU, hy⟩ := hsep x₀ hx₀
      refine ⟨_, ⟨y, rfl⟩, fun u hu => ?_, hy⟩
      show ψ (pairA F 0 ((x₀ + u) ⬝ᵥ y)) = ψ (pairA F 0 (x₀ ⬝ᵥ y))
      rw [add_dotProduct, pairA_zero_add, AddChar.map_add_eq_mul, hyU u hu, mul_one])
    a
    (by
      rintro χ ⟨y, rfl⟩ g hg
      show l (pureA F f₀ _) = l (pureA F f₀ g)
      rw [← hinv (fun i => pairA F 0 (y i)) (pureA F f₀ g) (mem_schA f₀ hg)]
      congr 1
      funext x
      simp [pureA, dot_pairA_fin, mul_left_comm])
  refine ⟨c, fun φ hφ => ?_⟩
  induction hφ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    obtain ⟨α, hα⟩ := harch g hg
    have hαc : α = c * g 0 := by
      have e1 := hα f₀
      rw [hf₀, mul_one] at e1
      rw [← e1]
      exact hc g hg
    rw [hα f, hαc, pureA_zero]
    ring
  | zero => simp
  | add φ φ' _ _ h h' => rw [map_add (f := _), h, h', Pi.add_apply, mul_add]
  | smul s φ _ h => rw [map_smul, h, Pi.smul_apply, smul_eq_mul, smul_eq_mul]; ring

end GlobalTheory.CharInvForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartCharacterIsLogarithmStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_character_is_logarithm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), ∀ χ : PS X.O 1 (chD Ch.ch), ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) χ → IsCharLog (fgl Ch X) (fun j => algebraMap X.O X.C (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl χ j)) := by
  first | exact @GlobalTheory.CharLogOfChar.isCharLog_dl | exact GlobalTheory.CharLogOfChar.isCharLog_dl | (intros; apply GlobalTheory.CharLogOfChar.isCharLog_dl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocal
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.RestCofactor

variable {F : Type} [Field F] [NumberField F]

def shiftFin (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) (y : κ → Af F) : κ → Af F :=
  fun i => y i + (singleFin v (x₀ i) - singleFin v (evalV F v (y i)))

theorem evalV_shiftFin (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) (y : κ → Af F) (i : κ) :
    evalV F v (shiftFin v x₀ y i) = x₀ i := by
  simp only [shiftFin, map_add (f := _), map_sub, evalV_singleFin_self]
  abel

theorem shiftFin_back (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) (y : κ → Af F) :
    shiftFin v (fun i => evalV F v (y i)) (shiftFin v x₀ y) = y := by
  funext i
  rw [shiftFin, evalV_shiftFin]
  simp only [shiftFin]
  abel

theorem continuous_shiftFin (v : Pl (F := F)) {κ : Type} :
    Continuous fun p : (κ → Fv F v) × (κ → Af F) => shiftFin v p.1 p.2 := by
  have hev : Continuous (evalV F v) := RestrictedProduct.continuous_eval v
  refine continuous_pi fun i => ?_
  have h2 : Continuous fun p : (κ → Fv F v) × (κ → Af F) => p.2 i := (continuous_apply i).comp continuous_snd
  have h1 : Continuous fun p : (κ → Fv F v) × (κ → Af F) => p.1 i := (continuous_apply i).comp continuous_fst
  exact h2.add (((continuous_singleFin v).comp h1).sub ((continuous_singleFin v).comp (hev.comp h2)))

theorem mem_SB_shift (v : Pl (F := F)) {κ : Type} (x₀ : κ → Fv F v) {φ' : (κ → Fv F v) → ℂ}
    (hφ' : φ' ∈ SB (κ → Fv F v)) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    (fun y : κ → Af F => φ' (fun i => evalV F v (y i)) * g (shiftFin v x₀ y)) ∈ SB (κ → Af F) := by
  have hev : Continuous (evalV F v) := RestrictedProduct.continuous_eval v
  have hE : Continuous fun y : κ → Af F => fun i => evalV F v (y i) :=
    continuous_pi fun i => hev.comp (continuous_apply i)
  have hS : Continuous (shiftFin v x₀) :=
    (continuous_shiftFin v).comp (continuous_const.prodMk continuous_id)
  refine ⟨(hφ'.1.comp_continuous hE).mul (hg.1.comp_continuous hS), ?_⟩
  have hK : IsCompact ((fun p : (κ → Fv F v) × (κ → Af F) => shiftFin v p.1 p.2) ''
      (tsupport φ' ×ˢ tsupport g)) := (IsCompact.prod hφ'.2 hg.2).image (continuous_shiftFin v)
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  have ha : φ' (fun i => evalV F v (y i)) ≠ 0 := left_ne_zero_of_mul hne
  have hb : g (shiftFin v x₀ y) ≠ 0 := right_ne_zero_of_mul hne
  exact hy ⟨(fun i => evalV F v (y i), shiftFin v x₀ y),
    ⟨subset_tsupport _ ha, subset_tsupport _ hb⟩, shiftFin_back v x₀ y⟩

theorem rest_of_rest : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (φ φ' : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ), φ ≠ 0 → φ' ∈ SB (κ → Fv F v) →
    Rest (evFin F v) φ r → Rest (evFin F v) φ' r := by
  intro F _ _ κ _ v φ φ' r hφ hφ' hr
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hφ
  refine ⟨hr.1, ?_⟩
  let z : (κ → AF F) → κ → AF F := fun x i =>
    pairA F 0 (singleFin v (x₀ i) - singleFin v (evalV F v (x i).2))
  have hz : ∀ x, At (evFin F v) (z x) := by
    intro x u hu
    funext i
    refine Prod.ext ?_ ?_
    · change u.1 * 0 = 0
      exact mul_zero _
    · change u.2 * (singleFin v (x₀ i) - singleFin v (evalV F v (x i).2)) = 0
      refine af_ext fun w => ?_
      rw [map_mul, map_zero]
      by_cases hw : w = v
      · subst hw
        have : evalV F w u.2 = 0 := hu
        rw [this, zero_mul]
      · rw [map_sub, evalV_singleFin_ne hw, evalV_singleFin_ne hw, sub_zero, mul_zero]
  have h1 : ∀ x i, ((x + z x) i).1 = (x i).1 := fun x i => by
    change (x i).1 + 0 = (x i).1
    exact add_zero _
  have h2 : ∀ x i, ((x + z x) i).2 = shiftFin v x₀ (fun i => (x i).2) i := fun x i => rfl
  have hev : ∀ x i, evFin F v ((x + z x) i) = x₀ i := fun x i => by
    change evalV F v ((x + z x) i).2 = x₀ i
    rw [h2, evalV_shiftFin]
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun Φ x => φ' (fun i => evFin F v (x i)) * Φ (x + z x)
      map_add' := fun Φ Ψ => funext fun x => by simp only [Pi.add_apply]; ring
      map_smul' := fun c Φ => funext fun x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hL : schA F κ ≤ (schA F κ).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    refine Submodule.subset_span ⟨f, _, mem_SB_shift v x₀ hφ' hg, funext fun x => ?_⟩
    change φ' (fun i => evFin F v (x i)) * pureA F f g (x + z x) = _
    simp only [pureA, h1, h2]
    change _ = _ * (φ' (fun i => evFin F v (x i)) * _)
    ring
  have key : tens (evFin F v) φ' r = (φ x₀)⁻¹ • L (tens (evFin F v) φ r) := by
    funext x
    change φ' (fun i => evFin F v (x i)) * r x =
      (φ x₀)⁻¹ * (φ' (fun i => evFin F v (x i)) * (φ (fun i => evFin F v ((x + z x) i)) * r (x + z x)))
    have hx : φ x₀ ≠ 0 := hx₀
    simp only [hev, hr.1 x (z x) (hz x)]
    rw [mul_left_comm (φ x₀)⁻¹, ← mul_assoc (φ x₀)⁻¹, inv_mul_cancel₀ hx, one_mul]
  rw [key]
  exact Submodule.smul_mem _ _ (hL hr.2)

end GlobalTheory.RestCofactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilRepresentationLocalityFinitePlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilRepresentation_locality_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ g : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)), At (evFin F v) (GlobalTheory.InertDbl.matD g - 1) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), ∃ φ₁ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), Acts (evFin F v) (omd g) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityDbl.locality | exact GlobalTheory.WeilLocalityDbl.locality | (intros; apply GlobalTheory.WeilLocalityDbl.locality <;> assumption)
end

