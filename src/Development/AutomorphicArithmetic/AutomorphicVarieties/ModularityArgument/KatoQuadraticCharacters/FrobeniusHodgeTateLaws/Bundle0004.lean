module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0373
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerBAdmissibleHeckeCommute

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.CgAppr
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct
open UpperTheory.V.Z.Kato.Joint

namespace UpperTheory.V.Z.Kato.Joint.ThetaOperator

variable {l : ℕ} [Fact l.Prime]

private theorem cg_trans {n : ℕ} {x y z : Qbar l} (h1 : Cg n x y) (h2 : Cg n y z) : Cg n x z := by
  unfold Cg at *
  have e : x - z = (x - y) + (y - z) := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

private theorem cg_symm {n : ℕ} {x y : Qbar l} (h1 : Cg n x y) : Cg n y x := by
  unfold Cg at *
  rwa [norm_sub_rev]

private theorem cg_lin {n : ℕ} {x y : Qbar l} (a c : Qbar l) (hc : ‖c‖ ≤ 1) (h1 : Cg n x y) :
    Cg n (a + c * x) (a + c * y) := by
  unfold Cg at *
  have e : a + c * x - (a + c * y) = c * (x - y) := by ring
  rw [e, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans h1

private theorem cg_j {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {j : Ω →+* Qbar l} (hj : ∀ x ∈ A, ‖j x‖ ≤ 1)
    {n : ℕ} {x y : Ω} (h : CgA A l n x y) : Cg n (j x) (j y) := by
  obtain ⟨z, hz, e⟩ := h
  unfold Cg
  rw [← map_sub, e, map_mul, map_pow, map_natCast, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hj z hz)

private theorem norm_appr_sub_le_norm_pow (n : ℕ) (c : ℤ_[l]) :
    ‖((c.appr n : ℕ) : Qbar l) - ((c : ℤ_[l]) : Qbar l)‖ ≤ ‖((l : Qbar l)) ^ n‖ := by
  have e : ((c.appr n : ℕ) : Qbar l) - ((c : ℤ_[l]) : Qbar l)
      = algebraMap ℚ_[l] (PadicAlgCl l) (((-(c - ((c.appr n : ℕ) : ℤ_[l])) : ℤ_[l]) : ℚ_[l])) := by
    simp
  have e2 : ((l : Qbar l)) ^ n = algebraMap ℚ_[l] (PadicAlgCl l) (((l : ℚ_[l])) ^ n) := by simp
  rw [e, e2, PadicAlgCl.norm_extends, PadicAlgCl.norm_extends, PadicInt.padic_norm_e_of_padicInt, norm_neg]
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 (PadicInt.appr_spec n c)
  refine h.trans (le_of_eq ?_)
  rw [Padic.norm_p_pow]

private theorem cg_appr (n : ℕ) (c : ℤ_[l]) (x : Qbar l) (hx : ‖x‖ ≤ 1) :
    Cg n (((c.appr n : ℕ) : Qbar l) * x) (((c : ℤ_[l]) : Qbar l) * x) := by
  unfold Cg
  rw [← sub_mul, norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_appr_sub_le_norm_pow n c) (norm_nonneg _)).trans
    (by rw [mul_comm]; exact mul_le_of_le_one_left (norm_nonneg _) hx)

private theorem appr_zero' (n : ℕ) : (0 : ℤ_[l]).appr n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [PadicInt.appr]; simp [ih]

private theorem diam_cg {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (χ : ℕ → ℤ_[l]) (hS : Std A N w j) (n a : ℕ) (b : X.Fn l)
    (ha : a.Coprime N) (hb : InChi X N w χ b) (r : ℚ) :
    Cg n (j ((thN X A N l n 1 (X.diam N l a b)).coeff r))
      (((χ a : ℤ_[l]) : Qbar l) * j ((thN X A N l n 1 b).coeff r)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨hl, hl2, hlN, hN5, hw, hj⟩ := hS
  obtain ⟨hbB, hdiam⟩ := hb
  have hB1 : X.diam N l 1 b ∈ X.B N l w := by
    rw [hdiam 1 (Nat.coprime_one_left N)]
    exact Submodule.smul_mem _ _ hbB
  have hBa : X.diam N l a b ∈ X.B N l w := by
    rw [hdiam a ha]
    exact Submodule.smul_mem _ _ hbB
  have hψ := (_root_.GlobalTheory.CyclotomicQExpansion.thN_isThB Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w 1 hw
    (Nat.coprime_one_left N) b hbB).1
  have hθ := (_root_.GlobalTheory.CyclotomicQExpansion.thN_isThB Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w 1 hw
    (Nat.coprime_one_left N) (X.diam N l a b) hBa).1
  have hD : ∀ s : ℚ, (thN X A N l n 1 b).coeff s ∈ A := by
    obtain ⟨f, -, -, -, hd⟩ := hψ
    exact hd.1
  have hlin := GlobalTheory.T.theta_basis_linear_combination Ω ε X A N l n w (X.diam N l 1 b) (X.diam N l 1 b) hB1 hB1 (χ a) 0
    (thN X A N l n 1 b) (thN X A N l n 1 b) hψ hψ
  have e : X.act l (sgD N l 1) (X.diam N l a b) = χ a • X.diam N l 1 b + (0 : ℤ_[l]) • X.diam N l 1 b := by
    rw [zero_smul, add_zero, hdiam a ha, map_smul]
    rfl
  rw [e] at hθ
  have hmem : χ a • X.diam N l 1 b + (0 : ℤ_[l]) • X.diam N l 1 b ∈ X.B N l w :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hB1) (Submodule.smul_mem _ _ hB1)
  have hu := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w hw _ hmem _ _ hθ hlin r
  have h1 := cg_j hj hu
  rw [appr_zero'] at h1
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, Nat.cast_zero, zero_smul, add_zero,
    smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast] at h1
  exact cg_trans h1 (cg_appr n (χ a) _ (hj _ (hD r)))

end UpperTheory.V.Z.Kato.Joint.ThetaOperator

private theorem norm_natCast_pow_le_one {l : ℕ} [Fact l.Prime] (q k : ℕ) : ‖((q : Qbar l)) ^ k‖ ≤ 1 := by
  have e : ((q : Qbar l)) ^ k = algebraMap ℚ_[l] (PadicAlgCl l) (((q : ℤ) : ℚ_[l]) ^ k) := by simp
  rw [e, PadicAlgCl.norm_extends, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (Padic.norm_int_le_one _)

private theorem coeff_div_prime_eq_zero_of_not_dvd_of_isLat {Ω : Type} [Field Ω] (φ : HahnSeries ℚ Ω) (hL : IsLat 1 φ) {q i : ℕ}
    (hq : q.Prime) (hnd : ¬ q ∣ i) : φ.coeff ((i : ℚ) / q) = 0 := by
  by_contra h
  have hden := hL _ h
  rw [Nat.cast_one, one_mul] at hden
  have key : (((i : ℚ) / q).num : ℚ) = (i : ℚ) / q := Rat.coe_int_num_of_den_eq_one hden
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have h2 : (i : ℚ) = q * ((i : ℚ) / q).num := by rw [key]; field_simp
  have h3 : (i : ℤ) = q * ((i : ℚ) / q).num := by exact_mod_cast h2
  exact hnd (Int.natCast_dvd_natCast.mp ⟨_, h3⟩)

open UpperTheory.V.Z.Kato.Joint.ThetaOperator in
theorem UpperTheory.V.Z.Kato.Joint.thOp :
    UpperTheory.V.Z.Kato.Joint.ThOp := by
  intro l _ Ω _ _ _ ε X A N w j χ hS n T b hT hb i
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hS' := hS
  obtain ⟨hl, hl2, hlN, hN5, hw, hj⟩ := hS'
  have hψ : ∀ m, IsThB X A N l m (X.act l (sgD N l 1) b) (thN X A N l m 1 b) ∧ IsLat 1 (thN X A N l m 1 b) :=
    fun m => _root_.GlobalTheory.CyclotomicQExpansion.thN_isThB Ω ε X A N l X.j_hol hl2 hlN hN5 hl m w 1 hw (Nat.coprime_one_left N) b hb.1
  have hrel := _root_.GlobalTheory.CyclotomicQExpansion.thN_hecke Ω ε X A N l X.j_hol hl2 hlN hN5 hl n w 1 hw (Nat.coprime_one_left N) b hb.1
  cases T with
  | T q =>
    obtain ⟨hqp, hqNl⟩ := hT
    have hqN : q.Coprime N :=
      Nat.Coprime.coprime_dvd_right (dvd_mul_right N l) ((Nat.Prime.coprime_iff_not_dvd hqp).2 hqNl)
    simp only [th, seqN, fop, Tower.op, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.EisM.To, GlobalTheory.EisM.Vo]
    have h1 := hrel.1 q hqp hqNl ((i : ℚ) / (1 : ℕ))
    rw [GlobalTheory.CyclotomicQExpansion.Api.hq_eq_uq_of_isAlgClosed hqp.pos (hψ n).2] at h1
    have h1' := cg_j hj h1
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, GlobalTheory.CyclotomicQExpansion.Api.coeff_uq hqp.pos,
      GlobalTheory.CyclotomicQExpansion.Api.coeff_vq hqp.pos, map_add, Nat.cast_one, div_one, Rat.den_natCast, if_true,
      one_mul, smul_eq_mul, nsmul_eq_mul, map_mul, map_pow, map_natCast] at h1'
    have hx : Cg n (j ((thN X A N l n q b).coeff ((i : ℚ) / q)))
        (((χ q : ℤ_[l]) : Qbar l) *
          (if q ∣ i then j ((thN X A N l n 1 b).coeff (((i / q : ℕ) : ℚ) / ((1 : ℕ) : ℚ))) else 0)) := by
      have ha := cg_j hj (hrel.2.2 q hqN ((i : ℚ) / q))
      have hc := cg_trans (cg_symm ha) (diam_cg X A N w j χ hS n q b hqN hb ((i : ℚ) / q))
      rw [one_mul] at hc
      split_ifs with hdiv
      · rwa [Nat.cast_one, div_one, Nat.cast_div hdiv (by exact_mod_cast hqp.ne_zero)]
      · rw [mul_zero]
        rwa [coeff_div_prime_eq_zero_of_not_dvd_of_isLat _ (hψ n).2 hqp hdiv, map_zero, mul_zero] at hc
    have key := cg_trans h1' (cg_lin _ _ (norm_natCast_pow_le_one q (w + 1)) hx)
    have hw2 : w + 2 - 1 = w + 1 := by omega
    simp only [Nat.cast_one, div_one, Nat.cast_mul, hw2]
    convert key using 2
    simp only [Nat.cast_one, div_one]
    ring
  | U =>
    show Cg n (j ((thN X A N l n 1 (X.heckeU l b)).coeff ((i : ℚ) / ((1 : ℕ) : ℚ))))
      (j ((thN X A N l n 1 b).coeff (((l * i : ℕ) : ℚ) / ((1 : ℕ) : ℚ))))
    have h2 := cg_j hj (hrel.2.1 ((i : ℚ) / (1 : ℕ)))
    simp only [GlobalTheory.CyclotomicQExpansion.Api.coeff_uq (Fact.out : l.Prime).pos, Nat.cast_one, div_one, Rat.den_natCast,
      if_true] at h2
    have h3 := cg_j hj (GlobalTheory.T.cgA_coeff_of_isThB_succ Ω ε X A N l hl2 hlN (by omega) hl n _ _ _ (hψ (n + 1)).1 (hψ n).1
      ((l : ℚ) * i))
    simp only [Nat.cast_one, div_one, Nat.cast_mul]
    exact cg_trans h2 h3
  | D d =>
    simp only [th, seqN, fop, Tower.op, LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply,
      smul_eq_mul]
    exact diam_cg X A N w j χ hS n d b hT hb _

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.CgpTrans
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

variable {l : ℕ} [Fact l.Prime]

private theorem cgp_refl (n : ℕ) (x : Qbar l) : Cg n x x := by simp [Cg]

private theorem cgp_symm {n : ℕ} {x y : Qbar l} (h : Cg n x y) : Cg n y x := by
  unfold Cg at *
  rwa [norm_sub_rev]

private theorem cgp_add {n : ℕ} {x y x' y' : Qbar l} (h : Cg n x y) (h' : Cg n x' y') : Cg n (x + x') (y + y') := by
  unfold Cg at *
  rw [add_sub_add_comm]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

private theorem cgp_trans {n : ℕ} {x y z : Qbar l} (h : Cg n x y) (h' : Cg n y z) : Cg n x z := by
  unfold Cg at *
  rw [← sub_add_sub_cancel x y z]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

private theorem cgp_mul {n : ℕ} {a x y : Qbar l} (ha : ‖a‖ ≤ 1) (h : Cg n x y) : Cg n (a * x) (a * y) := by
  simpa using cg_mul_left (k := 0) (Nat.zero_le _) (by simpa using ha) h

private theorem fop_cg {k n : ℕ} {χ : ℕ → Qbar l} (hχ : ∀ d, ‖χ d‖ ≤ 1) (T : Letter) {f g : ℕ → Qbar l}
    (h : ∀ i, Cg n (f i) (g i)) (i : ℕ) : Cg n (fop k l χ T f i) (fop k l χ T g i) := by
  cases T with
  | T q =>
    show Cg n (GlobalTheory.EisM.To k (χ q) q f i) (GlobalTheory.EisM.To k (χ q) q g i)
    unfold GlobalTheory.EisM.To GlobalTheory.EisM.Vo
    refine cgp_add (h _) (cgp_mul ?_ ?_)
    · rw [norm_mul, norm_pow]
      exact mul_le_one₀ (hχ q) (by positivity)
        (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _))
    · split_ifs
      · exact h _
      · exact cgp_refl _ _
  | U => exact h _
  | D d => exact cgp_mul (hχ d) (h i)

theorem thP : ThP := by
  intro hOp hStab l _ Ω _ _ _ ε X A N w j χ hS P hP
  set F := FreeAlgebra.lift (Qbar l) (fop (w + 2) l fun d => ((χ d : ℤ_[l]) : Qbar l)) with hF
  set G := FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) with hG
  have hχ : ∀ d, ‖((χ d : ℤ_[l]) : Qbar l)‖ ≤ 1 := fun d => by
    rw [norm_algebraMap']
    exact (χ d).2
  have hw : ∀ x ∈ Submonoid.closure (FreeAlgebra.ι (Qbar l) '' {T | GlobalTheory.KZ.admitted N l T}), ∀ n : ℕ,
      (∀ f g : ℕ → Qbar l, (∀ i, Cg n (f i) (g i)) → ∀ i, Cg n (F x f i) (F x g i)) ∧
      ∀ b, InChi X N w χ b → ∃ b', InChi X N w χ b' ∧
        G x ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) = (1 : Qbar l) ⊗ₜ[ℤ_[l]] b' ∧
        ∀ i, Cg n (F x (th X A N j n b) i) (th X A N j n b' i) := by
    intro x hx n
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨T, hT, rfl⟩ := hx
      rw [hF, hG, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
      refine ⟨fun f g h i => fop_cg hχ T h i, fun b hb => ⟨X.op N l T b,
        hStab l Ω ε X N w χ hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2.1 T b hT hb, ?_,
        fun i => cgp_symm (hOp l Ω ε X A N w j χ hS n T b hT hb i)⟩⟩
      rw [Tower.opV, LinearMap.baseChange_tmul]
    | one =>
      rw [map_one, map_one]
      exact ⟨fun f g h i => h i, fun b hb => ⟨b, hb, rfl, fun i => cgp_refl _ _⟩⟩
    | mul x y _ _ hx hy =>
      rw [map_mul, map_mul]
      refine ⟨fun f g h i => hx.1 _ _ (hy.1 f g h) i, fun b hb => ?_⟩
      obtain ⟨b', hb', e', c'⟩ := hy.2 b hb
      obtain ⟨b'', hb'', e'', c''⟩ := hx.2 b' hb'
      refine ⟨b'', hb'', ?_, fun i => cgp_trans (hx.1 _ _ c' i) (c'' i)⟩
      rw [Module.End.mul_apply, e', e'']
  have hP' : P ∈ Submodule.span (Qbar l)
      (Submonoid.closure (FreeAlgebra.ι (Qbar l) '' {T | GlobalTheory.KZ.admitted N l T}) : Set (FreeAlgebra (Qbar l) Letter)) := by
    rw [← Algebra.adjoin_eq_span]
    exact hP
  clear hP
  induction hP' using Submodule.span_induction with
  | mem x hx =>
    refine ⟨0, fun n _ Θ hΘ b hb i => ?_⟩
    obtain ⟨b', hb', e', c'⟩ := (hw x hx n).2 b hb
    rw [e', Nat.sub_zero]
    exact cgp_trans (c' i) (cgp_symm (hΘ b' hb'.1 i))
  | zero =>
    refine ⟨0, fun n _ Θ hΘ b hb i => ?_⟩
    simp only [map_zero, LinearMap.zero_apply]
    exact cgp_refl _ _
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c + d, fun n hn Θ hΘ b hb i => ?_⟩
    simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
    exact cgp_add (cg_mono (by omega) (hc n (by omega) Θ hΘ b hb i))
      (cg_mono (by omega) (hd n (by omega) Θ hΘ b hb i))
  | smul a x _ hx =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨k, hk⟩ := exists_le_l_pow l ‖a‖
    refine ⟨c + k, fun n hn Θ hΘ b hb i => ?_⟩
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Nat.sub_sub]
    exact cg_mul_left (by omega) hk (hc n (by omega) Θ hΘ b hb i)

end UpperTheory.V.Z.Kato.Joint

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiStab
section
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.chiStab :
    UpperTheory.V.Z.Kato.Joint.ChiStab := by
  intro l hp Ω _ _ _ ε X N w χ hl hlN hN hw T b hT hb
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hlN).symm
  obtain ⟨φ, h1, h2⟩ := X.j_hol
  refine ⟨_root_.GlobalTheory.KZ.B_stable_op ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T hT b hb.1, fun d hd => ?_⟩
  have h := _root_.GlobalTheory.KZ.B_op_comm ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T (GlobalTheory.KZ.Letter.D d) hT hd b hb.1
  change X.op N l T (X.diam N l d b) = X.diam N l d (X.op N l T b) at h
  rw [← h, hb.2 d hd, map_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.FinSuppCompLift
section
open UpperTheory.V.Z.Kato.Joint

section

open Formalism.ConjugateSelfDual GlobalTheory.KZ GlobalTheory.KummerEisensteinGalois GlobalTheory.LambdaValuationPowers UpperTheory.V.HV

variable {l : ℕ} [Fact l.Prime]

private theorem finSupp_comp_fop (k : ℕ) (χ : ℕ → Qbar l) (T : Letter)
    (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (h : FinSupp lam) : FinSupp (lam ∘ₗ fop k l χ T) := by
  obtain ⟨S, hS⟩ := h
  cases T with
  | T q =>
    refine ⟨S.image (q * ·) ∪ S.image (· / q), fun f hf => ?_⟩
    rw [LinearMap.comp_apply]
    apply hS
    intro n hn
    show GlobalTheory.EisM.To k (χ q) q f n = 0
    have h1 : f (q * n) = 0 := hf _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩))
    have h2 : f (n / q) = 0 := hf _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩))
    simp [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, h1, h2]
  | U =>
    refine ⟨S.image (l * ·), fun f hf => ?_⟩
    rw [LinearMap.comp_apply]
    apply hS
    intro n hn
    show GlobalTheory.EisM.Uo l f n = 0
    exact hf _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
  | D d =>
    refine ⟨S, fun f hf => ?_⟩
    rw [LinearMap.comp_apply]
    apply hS
    intro n hn
    show (χ d • f) n = 0
    simp [hf n hn]

private theorem finSupp_comp_lift (k : ℕ) (χ : ℕ → Qbar l) (P : FreeAlgebra (Qbar l) Letter) :
    ∀ lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l, FinSupp lam →
      FinSupp (lam ∘ₗ FreeAlgebra.lift (Qbar l) (fop k l χ) P) := by
  induction P using FreeAlgebra.induction with
  | grade0 r =>
    intro lam h
    rw [AlgHom.commutes]
    have hr : lam ∘ₗ algebraMap (Qbar l) (Module.End (Qbar l) (ℕ → Qbar l)) r = r • lam := by
      ext f
      simp [Module.algebraMap_end_apply]
    rw [hr]
    exact FinSupp.smul h r
  | grade1 x =>
    intro lam h
    rw [FreeAlgebra.lift_ι_apply]
    exact finSupp_comp_fop k χ x lam h
  | mul a b ha hb =>
    intro lam h
    rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
    exact hb _ (ha lam h)
  | add a b ha hb =>
    intro lam h
    rw [map_add (f := _), LinearMap.comp_add]
    exact FinSupp.add (ha lam h) (hb lam h)

private theorem exists_pow_mul_le (x : Qbar l) : ∃ k : ℕ, ‖((l : ℕ) : Qbar l) ^ k * x‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_le_l_pow l ‖x‖
  refine ⟨k, ?_⟩
  rw [norm_mul, norm_l_pow]
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  calc ((l : ℝ))⁻¹ ^ k * ‖x‖ ≤ ((l : ℝ))⁻¹ ^ k * (l : ℝ) ^ k := by gcongr
    _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hl.ne', one_pow]

end

open Formalism.ConjugateSelfDual GlobalTheory.KZ GlobalTheory.KummerEisensteinGalois GlobalTheory.LambdaValuationPowers UpperTheory.V.HV in
theorem UpperTheory.V.Z.Kato.Joint.finP :
    UpperTheory.V.Z.Kato.Joint.FinP := by
  classical
  intro hub l _ ι k N B cc χE c₀ P _
  let lam₀ : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l :=
    ∑ n ∈ Finset.range B, ι.symm (cc n) • LinearMap.proj n
  have hlam₀ : ∀ a : ℕ → Qbar l, lam₀ a = ι.symm (GlobalTheory.EisM.lam B cc fun i => ι (a i)) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      simp [lam₀, GlobalTheory.EisM.lam, map_sum, map_mul, LinearMap.sum_apply]
  have hfs₀ : FinSupp lam₀ := by
    refine ⟨Finset.range B, fun f hf => ?_⟩
    rw [hlam₀, GlobalTheory.EisM.lam, Finset.sum_eq_zero, map_zero]
    intro n hn
    simp [hf n hn]
  let lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l := lam₀ ∘ₗ FreeAlgebra.lift (Qbar l) (fop k l χE) P
  have hfs : FinSupp lam := finSupp_comp_lift k χE P lam₀ hfs₀
  obtain ⟨S, hS⟩ := hfs
  choose e he using exists_pow_mul_le (l := l)
  let g : ℕ → Qbar l := fun i => ((l : ℕ) : Qbar l) ^ e (lam (Pi.single i 1)) * lam (Pi.single i 1)
  obtain ⟨c, hc₀, -, hcF⟩ := hub l c₀ c₀ (S.image g) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact he _)
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine ⟨lam₀, lam, c, hc₀, hfs₀, ⟨S, hS⟩, ?_, hlam₀, fun a => rfl⟩
  intro i σ hσ _
  by_cases hi : i ∈ S
  · have hy := hσ _ (hcF _ (Finset.mem_image_of_mem g hi))
    have hne : ((l : ℕ) : Qbar l) ^ e (lam (Pi.single i 1)) ≠ 0 := by
      intro h0
      have h1 := congrArg norm h0
      rw [norm_l_pow, norm_zero] at h1
      exact pow_ne_zero _ (inv_ne_zero hl.ne') h1
    simp only [g, map_mul, map_pow, map_natCast] at hy
    exact mul_left_cancel₀ hne hy
  · have h0 : lam (Pi.single i 1) = 0 :=
      hS _ (fun s hs => Pi.single_eq_of_ne (by rintro rfl; exact hi hs) 1)
    rw [h0, map_zero]
end

